# B5: standard doubled ladder, uniform base proof

**Status: PROVED for every even integer \(d\ge4\).** This note proves
BLUEPRINT L20–L24 for B5, including recurrence and the constants
\[
c_1=0,\qquad c_2=-d(d+3)/2.
\]
The explicit recurrence rank is in §7. The harmonic rotation already
proved by the parent investigation transfers all these results to B6.

The only source is the algorithmic formula BLUEPRINT A1(B5); the paper's
proof is neither read nor used.

## 1. Formula and rows

Write
\[
\begin{gathered}
T=d^2+2d-1,\quad U=(2d,2),\quad V=(1-d,d+1),\quad s(x,y)=x-dy,\\
Q(y)=-y(y-1)/2,\quad
P(x)=\min(0,x-1)+\min(0,d+1-x),\\
J(x,y)=\mathbf1_{\{x+y=d+2,\ 2\le y\le d\}}
       +\mathbf1_{\{(x,y)=(0,0)\text{ or }(d+2,d+2)\}}.
\end{gathered}
\]
On the B5 domain \(D\), the value is exactly
\[
o(x,y)=Q(y)+P(x)+\max(x+y-d-2,0)+J(x,y).
\tag{B5.1}
\]
The two summands defining \(J\) have disjoint supports.

Directly from A1, every row is an integer interval:

| Row \(y\) | Inclusive range of \(x\) |
|---|---|
| \(0\) | \(0\le x\le d-1\) |
| \(1\) | \(0\le x\le2d\) |
| \(2\) | \(-1\le x\le2d\) |
| \(3\le y\le d-1\) | \(1-y\le x\le2d+3-y\) |
| \(d\) | \(2-d\le x\le d+3\) |
| \(d+1\) | \(2-d\le x\le d+2\) |
| \(d+2\) | \(3\le x\le d+2\) |

For \(d=4\) the middle row range contains the single row \(y=3\);
all other rows remain distinct. Equivalently the rows \(1\le y\le d+1\)
have endpoints
\[
L(y)=\max(2-d,1-y),\qquad R(y)=\min(2d,2d+3-y).
\]
Counting the displayed rows gives
\[
|D|=2d+(2d+1)+(2d+2)+(d-3)(2d+3)+(2d+2)+(2d+1)
    =2d^2+7d-3.
\tag{B5.2}
\]

## 2. Complete overlap classification

The only nonzero lattice vectors joining two points of \(D\) are
\(\pm U,\pm V\).

Indeed \(D\) has \(x\)-span \(3d-2\) and \(y\)-span \(d+2\). It also has
\[
1-T\le s(x,y)\le d.
\tag{B5.3}
\]
For the upper bound, the row \(y=0\) has \(s\le d-1\), while at \(y\ge1\)
the bound \(x\le2d\) gives \(s\le d\). For the lower bound, rows
\(y\le d+1\) satisfy \(x\ge2-d\), so
\(s\ge2-d-d(d+1)=1-T\); the last row satisfies
\(s\ge3-d(d+2)=2-T\).

If \(z,z+aU+bV\in D\), then their level difference is \(-bT\).
The span \(T+d-1<2T\) in (B5.3) forces \(|b|\le1\).
If \(b=0\), the \(x\)-span forces \(|a|\le1\).
If \(b=1\), the \(y\)-difference \(2a+d+1\le d+2\) forces \(a\le0\).
If \(a\le-1\), the \(x\)-difference
\(2ad+1-d\le1-3d\) has absolute value at least \(3d-1\), too large.
Thus \(a=0\). The case \(b=-1\) follows by exchanging the points.

The sources \(z\) for positive overlaps are exactly:

| Displacement | Sources \(z\), with \(z,z+\text{displacement}\in D\) | Count |
|---|---|---|
| \(U\) | \((0,0)\); \((1-y,y)\), \(1\le y\le d-1\); \((2-d,d)\) | \(d+1\) |
| \(V\) | \((x,0)\), \(1\le x\le d-1\); \((x,1)\), \(d+2\le x\le2d\) | \(2d-2\) |

For \(U\), intersect the row-\(y\) interval with the row-\(y+2\)
interval shifted by \(-2d\). The intersection is a singleton \(0\)
at \(y=0\), the singleton \(1-y\) for \(1\le y\le d-1\),
and the singleton \(2-d\) at \(y=d\); other rows cannot overlap.
For \(V\), only source rows zero and one are possible, and intersecting
their intervals with the target intervals gives precisely the two ranges
displayed above. This proves exhaustiveness, not only inclusion.

## 3. Compatibility and covering

On the \(U\)-overlap, the two values agree. At its first source they are
both zero. At \((1-y,y)\), \(1\le y\le d-1\), the source value is
\[
Q(y)-y=-y(y+1)/2,
\]
whereas the target has
\[
Q(y+2)+(y-d)+(d+1)=Q(y+2)+y+1=-y(y+1)/2.
\]
At the last source \((2-d,d)\) the value is
\[
Q(d)+1-d=1-d(d+1)/2.
\]
Its target is \((d+2,d+2)\), where (B5.1) gives
\[
Q(d+2)-1+(d+2)+1=Q(d+2)+d+2=1-d(d+1)/2.
\]
Thus the \(U\)-increment is \(c_1=0\).

For the \(V\)-overlap in row zero, both nonquadratic terms at the source
vanish, so \(o(x,0)=0\). At the target \((x+1-d,d+1)\),
\[
o(x+1-d,d+1)=Q(d+1)+x-d=x-d(d+3)/2=s(x,0)+c_2.
\]
For its overlap in row one, \(d+2\le x\le2d\), the negative term
\(d+1-x\) cancels the positive term \(x-d-1\), so \(o(x,1)=0\).
At the target \((x+1-d,d+2)\),
\[
o(x+1-d,d+2)=Q(d+2)+x-d+1
            =x-d-d(d+3)/2=s(x,1)+c_2.
\]
This proves compatibility for positive generators, hence for negative
ones by reversing the equality. Section 2 shows that these are every
nontrivial pair in the same lattice class, so the full pairwise
compatibility hypothesis of BLUEPRINT L13 is satisfied.

No lattice class has three representatives in \(D\). Otherwise two of
the differences from one representative belong to
\(\{U,-U,V,-V\}\), and their difference is one of
\(\pm2U,\pm2V,\pm U\pm V\), none of which belongs to that list.
This contradicts Section 2.
Every double class is therefore counted exactly once by the positive
overlap pairs. By (B5.2), the number of represented classes is
\[
|D|-(d+1)-(2d-2)=2d^2+4d-2=2T.
\]
Since the quotient \(\mathbb Z^2/\langle U,V\rangle\) has exactly \(2T\)
classes, every class is represented. The maximum multiplicity is two.

BLUEPRINT L13 now gives the well-defined integer extension \(E\),
the prescribed growth \(M(1,d)\), and full periodicity with the displayed
constants. This proves B5 L20 and L23 uniformly.

## 4. Reflection symmetry, independent of superharmonicity

Put
\[
w=(d+2,d+2),\qquad C=-(d+2)(d-1)/2=1-d(d+1)/2.
\]
The domain \(D\) is invariant under \(z\mapsto w-z\), as can be checked
from either A1's inequalities and deleted rows or the row table.
The two terms of \(P\) exchange, the support of \(J\) is invariant, and
\[
\begin{aligned}
Q(d+2-y)-Q(y)&=-(d+2)(d+1)/2+(d+1)y,\\
\max(d+2-x-y,0)-\max(x+y-d-2,0)&=d+2-x-y.
\end{aligned}
\]
Adding gives the exact tile identity
\[
o(w-z)-o(z)=-s(z)+C.
\tag{B5.4}
\]

This also holds for \(E\) globally. To see this without assuming anything
about its Laplacian, define \(F(z)=E(w-z)+s(z)-C\).
It agrees with \(E\) on \(D\). Under \(U\), both \(F\) and \(E\) have
increment zero. Under \(V\), the rule for \(E\) gives
\[
F(z+V)-F(z)=s(z)-s(w)-2T-c_2=s(z)+c_2,
\]
because \(s(w)+2T+2c_2=0\). Thus \(F\) and \(E\) have the same
periodicity rule and agree on a domain representing every class;
they agree globally.

As \(w\) is even and affine functions are harmonic, (B5.4) yields
\[
\Delta E(w-z)=\Delta E(z).
\tag{B5.5}
\]
This proves B5 L24 and permits reflected boundary cases in the next
section.

## 5. Exact Laplacian table

Everything below is stated in the native bit-zero coordinates of B5.

For **even** \(z=(x,y)\in D\), the Laplacian equals \(-1\) precisely on
the following three disjoint sets:
\[
\begin{aligned}
A_1&=\{(1,y):1\le y\le d-1,\ y\text{ odd}\},\\
A_2&=\{(d+1,y):3\le y\le d+1,\ y\text{ odd}\},\\
A_3&=\{(x,y):x+y=d+2,\ 2\le y\le d\}.
\end{aligned}
\tag{B5.6}
\]
It equals zero on all other even cells of \(D\).

For **odd** cells, let the lower vertical boundary be
\[
\begin{split}
B_-={}&\{(x,1-x):2-d\le x\le-1\}\\
&{}\cup\{(x,0):1\le x\le d-1,\ x\text{ odd}\}\\
&{}\cup\{(x,1):d\le x\le2d,\ x\text{ even}\},
\end{split}
\tag{B5.7}
\]
and put \(B_+=w-B_-\). Define
\[
\begin{aligned}
Z_1&=\{(x,y):x+y=d+1,\ 1\le y\le d-1\},\\
Z_2&=\{(x,y):x+y=d+3,\ 3\le y\le d+1\},\\
Z_3&=\{(0,1),(d+2,d+1)\}.
\end{aligned}
\tag{B5.8}
\]
The Laplacian of an odd \(z\in D\) is zero exactly on
\[
B_-\cup B_+\cup Z_1\cup Z_2\cup Z_3,
\tag{B5.9}
\]
and equals \(-1\) elsewhere.

### 5.1 Stars contained in \(D\)

At an even cell whose horizontal neighbors lie in \(D\), the second
difference of (B5.1) is
\[
-\mathbf1_{\{x=1\}}-\mathbf1_{\{x=d+1\}}
+\mathbf1_{\{x+y=d+2\}}
-2\mathbf1_{\{x+y=d+2,\ 2\le y\le d\}}.
\]
The neighboring cells have odd parity, so none is a nonzero \(J\)-cell;
the central correction contributes only its \(-2\) term.
The possible diagonal cells of \(D\) have \(1\le y\le d+1\).
At \(y=1,d+1\), the \(+1\) kink cancels the corresponding \(x=d+1\)
or \(x=1\) kink. At \(2\le y\le d\), it combines with the \(-2\)
correction to give \(-1\). Off the diagonal, only the two vertical
kinks contribute. This is exactly (B5.6).

At an odd cell with both vertical neighbors in \(D\), the quadratic
term contributes \(-1\). Neither \(P\) nor the positive-part term
contributes, since the positive-part kink lies on the even diagonal
\(x+y=d+2\). The central \(J\) is zero. Its upper neighbor contributes
one exactly on \(Z_1\), its lower neighbor exactly on \(Z_2\), and
a corner neighbor exactly on \(Z_3\).
These three sets are pairwise disjoint for \(d\ge4\), so the result is
zero on their union and \(-1\) otherwise.

### 5.2 Horizontal exits

The row endpoints show that the only even cells with a missing horizontal
neighbor are
\[
(0,0),\quad(2d,2),\quad(2-d,d),\quad(d+2,d+2).
\]
The first two differ by \(U\), as do the last two. Periodicity of the
Laplacian reduces the check to \((0,0)\) and \((2-d,d)\).

At \((0,0)\), the right neighbor has value zero. Its missing left
neighbor is lattice-equivalent by \(+U\) to \((2d-1,2)\), whose value is
\[
Q(2)+(2-d)+(d-1)=0.
\]
The center value is also zero, so the Laplacian is zero.

At \(z=(2-d,d)\), the center value is \(C=1-d(d+1)/2\).
Its right neighbor has value \(C+1\). The missing left neighbor becomes
\((d+1,d+2)\) after \(+U\), and has value
\[
Q(d+2)+(d+1)=-d(d+1)/2=C-1.
\]
Thus the Laplacian is again zero. These four cells are outside all
three sets in (B5.6), so the claimed even table is established everywhere.

### 5.3 Vertical exits

The column endpoints, or the row inequalities, show that the odd cells
missing a lower neighbor are exactly \(B_-\). The odd cells missing an
upper neighbor are exactly \(B_+\), by domain reflection.
The two boundary sets are disjoint. It suffices by (B5.5) to check \(B_-\).

* For \(z=(x,1-x)\), \(2-d\le x\le-1\), write \(y=1-x\).
  The center value is \(Q(y)+x-1\), and the upper neighbor has value
  \(Q(y+1)+x-1\); its increment from the center is \(-y=x-1\).
  The missing lower neighbor becomes
  \((x+2d,2-x)\) after \(+U\), whose value is
  \(Q(y+1)+1-x\). Its increment from the center is \(1-x=y\).
  The two increments sum to zero.
* For \(z=(x,0)\), \(1\le x\le d-1\) odd, both center and upper
  neighbor have value zero. The lower neighbor \(z-e_2\), shifted by
  \(+V\), is \(r=(x+1-d,d)\), with
  \(o(r)=Q(d)+x-d\). Since
  \(E(z-e_2)=o(r)-s(z-e_2)-c_2\), its value is
  \(Q(d)-2d-c_2=0\). Hence the Laplacian is zero.
* For \(z=(x,1)\), \(d\le x\le2d\) even, the center and upper
  neighbor also have value zero. At \(x=d\), the upper value is zero
  because the diagonal correction cancels \(Q(2)=-1\); at
  \(x\ge d+2\), the two piecewise-linear terms sum to one and again
  cancel \(Q(2)\).
  The lower neighbor becomes \(r=(x+1-d,d+1)\) after \(+V\), where
  \(o(r)=Q(d+1)+x-d\). Its extension value is
  \(Q(d+1)-d-c_2=0\), so the Laplacian is zero.

Reflection handles every upper exit. Combined with §5.1, this proves
(B5.9), hence B5 L21 uniformly.

## 6. Consequences and verification status

There are \(2d-1\) even AND classes and \(d^2-2d+2\) odd AND classes,
for \(d^2+1\) in total. For the even count, the three disjoint sets
in (B5.6) have sizes \(d/2,d/2,d-1\), and none is an overlap source or
target with nonzero Laplacian.

For the odd count, the row table gives
\[
|D\cap\{\text{odd}\}|=d+4(d+1)+(d-3)(d+2)=d^2+4d-2.
\]
Exactly \(d-1\) of the \(U\)-pairs and \(d\) of the \(V\)-pairs
are odd, so there are \(T\) odd classes. The disjoint boundary sets
\(B_-,B_+\) each contain \(2d-1\) points; each \(Z_1,Z_2\) contains
\(d-1\), and \(Z_3\) contains two. Their only intersections are
\(B_-\cap Z_1=\{(d,1)\}\) and
\(B_+\cap Z_2=\{(2,d+1)\}\). Thus (B5.9) contains \(6d-4\)
odd representatives. Every odd overlap pair has both endpoints in
that union: the \(U\)-sources lie on the lower diagonal or at
\((0,1)\), and the odd \(V\)-sources lie on the bottom row or
the lower shelf. Therefore the number of odd OR classes is
\((6d-4)-(2d-1)=4d-3\), and the number of odd AND classes is
\(T-(4d-3)=d^2-2d+2\), as asserted.

The proof uses only exhaustive interval intersections, elementary
quadratic identities, and the boundary exits specified above. In
particular it does not extrapolate from a finite parameter range.

The independent ad hoc verification checked all 51 even parameters
\(d=4,6,\ldots,100,128,200\), totaling 476139 tile cells. It verified
the domain size, quotient coverage, maximum multiplicity two, all
overlap increments, the exact Laplacian classification (B5.6)–(B5.9),
the reflection identity, and both parity-specific AND counts. It also
compared the formula against the independent Python transcription of
the algorithm for every even \(d\le30\), with shift \((d-1,1)\).
All checks passed. The verification was initially executed as an
ad hoc command. Its reconstructed saved version is
`scripts/base_b5_uniform.py`; after memory recovered above the required
threshold, this saved script was rerun with `nice` and an immediate
memory guard. It reproduced the same 51-parameter, 476139-cell result.
The exact saved output is `data/base_b5_uniform_verification.json`;
the script also records its starting available memory. The formulas
and interval proofs above, not this finite check, prove the uniform
assertions.

## 7. Explicit uniform recurrence rank **[PROVED]**

The following is a new proof using only the domain and Laplacian tables
already established. It does not rely on a generic implication from
periodic acyclicity to existence of a rank with prescribed drift.

Put \(p=(x+y)\bmod2\), \(t=x+y\), and introduce the five special cells
\[
a=(0,0),\quad c=(2d,2),\quad
e=(2d,1),\quad f=(d+1,d+2),\quad b=(d+2,d+2).
\]
Define \(\rho_D:D\to\mathbb Z\) by the following **ordered** clauses:
the first applicable row is used.

| Condition | \(\rho_D(x,y)\) |
|---|---:|
| \(z=a\) or \(z=c\) | \(4\) |
| \(z=e\) or \(z=f\) | \(5\) |
| \(z=b\) | \(0\) |
| \(y=0\) or \(x\le0\) | \(p\) |
| \(y=d+2\), or \(y=1,\ x\ge d+2\), or \(x\le d,\ t\ge d+3\) | \(8+p\) |
| \(t\le d+1\) | \(8(d+1-x)+p\) |
| \(t=d+2,\ x\in\{1,d+1\}\) | \(8\) |
| \(t=d+2,\ x\notin\{1,d+1\}\) | \(8d\) |
| \(t\le2d+1\) | \(8(2d-x)+p\) |
| \(t=2d+2\) | \(8\) |
| \(t=2d+3\) | \(1\) |

These clauses cover \(D\). Indeed, after the first five rows fail,
\(x\ge1\), \(1\le y\le d+1\), and \(1\le t\le2d+3\).
The remaining rows partition that interval of \(t\). On \(t=d+2\),
the domain has \(1\le x\le d+1\), so its nonendpoint cells satisfy
\(2\le x\le d\).

### 7.1 Periodic consistency of the correction

All overlaps were listed in §2, so it suffices to compare their
\(\rho_D\)-values.

* The \(U\)-pair \(a,c\) has value \(4\) at both ends.
* At \((1-y,y)\), \(1\le y\le d-1\), the source has \(x\le0\)
  and odd parity, hence value \(1\). Its target has sum \(2d+3\)
  and also value \(1\).
* The last \(U\)-source \((2-d,d)\) and its target \(b\) both
  have value \(0\).
* For the \(V\)-source \((x,0)\), \(1\le x\le d-1\), the value
  is \(p\). Its target \((x+1-d,d+1)\) has first coordinate at
  most zero and the same parity, hence the same value \(p\).
* For the \(V\)-source \((x,1)\), \(d+2\le x\le2d-1\),
  both source and target \((x+1-d,d+2)\) have value \(8+p\).
  The final pair \(e,f\) has value \(5\) at both ends.

Thus \(\rho_D\) extends to a well-defined
\(\langle U,V\rangle\)-periodic integer function \(\rho\) on
\(\mathbb Z^2\). Set
\[
R(x,y)=6x+\rho(x,y).
\tag{B5.10}
\]
If \(q\) is an incoming neighbor of \(z\), the rank difference is
\[
R(q)-R(z)=6(q_x-z_x)+\rho(q)-\rho(z).
\tag{B5.11}
\]
When an incoming neighbor lies outside \(D\), the representative
specified below determines its periodic correction; its actual
first coordinate is still used in (B5.11). Translating an entire
star by a period does not change its rank differences.

We verify that both incoming neighbors have lower rank at every
AND-cell and at least one does at every OR-cell.

### 7.2 Even AND-cells: both horizontal neighbors decrease

The three cases are exactly (B5.6).

* On \(A_1\), the center is \((1,y)\), \(y\) odd,
  \(1\le y\le d-1\), and has correction \(8d\).
  The left correction is \(1\) and the right correction is
  \(8(d-1)+1=8d-7\). Their rank differences are
  \(-6+1-8d<0\) and \(-1\).
* On \(A_2\) below its last point, the center is
  \((d+1,y)\), \(3\le y\le d-1\), and has correction
  \(8(d-1)\). Its left correction is \(9\); its right
  correction is \(8(d-2)+1\). The differences are
  \(3-8(d-1)<0\) and \(-1\).
  At the final point \((d+1,d+1)\), the center correction is
  \(8\), the left correction is \(9\), and the right is \(1\);
  the differences are \(-5,-1\).
* On \(A_3\), write the center as \((x,d+2-x)\),
  \(2\le x\le d\). Its correction is \(8d\).
  The left correction is \(8(d+2-x)+1\), giving difference
  \(11-8x\le-5\).
  If \(x\le d-1\), the right correction is \(9\), giving
  \(15-8d<0\). If \(x=d\), the right correction is
  \(8(d-1)+1\), giving \(-1\).

Every neighbor in these cases belongs to \(D\).

### 7.3 Even OR-cells: one horizontal neighbor decreases

The following list exhausts the remaining even cells, using the
ordered clauses defining \(\rho_D\). Boundary representatives are
included wherever a chosen neighbor is outside \(D\).

| Center class | Chosen direction | Center correction | Chosen neighbor correction | Rank difference |
|---|---|---:|---:|---:|
| \(a,c\) | left | \(4\) | \(9\) | \(-1\) |
| \(b\) | left | \(0\) | \(5\) | \(-1\) |
| other \(x\le0\), except \((2-d,d)\) | left | \(0\) | \(1\) | \(-5\) |
| \((2-d,d)\) | left | \(0\) | \(5\) | \(-1\) |
| \(y=0,\ 2\le x\le d-2\) | left | \(0\) | \(1\) | \(-5\) |
| \(y=d+2,\ 4\le x\le d\) | left | \(8\) | \(9\) | \(-5\) |
| \(y=1,\ d+3\le x\le2d-1\) | left | \(8\) | \(9\) | \(-5\) |
| \(x\ge2,\ y\ge1,\ t\le d\) | right | \(8(d+1-x)\) | \(8(d-x)+1\) | \(-1\) |
| \((1,d+1)\) | left | \(8\) | \(1\) | \(-13\) |
| \((d+1,1)\) | left | \(8\) | \(9\) | \(-5\) |
| \(x\le d,\ y\le d+1,\ t\ge d+4\) | left | \(8\) | \(9\) | \(-5\) |
| \(x\ge d+2,\ y\ge2,\ t\le2d\) | right | \(8(2d-x)\) | \(8(2d-x-1)+1\) | \(-1\) |
| \(t=2d+2,\ x\ge d+2,\ y\ge3\) | right | \(8\) | \(1\) | \(-1\) |

The table is read after the AND cases and earlier rows have been
removed; thus, for example, its last row excludes \(c\). Parity in
each row is even, so displayed inclusive intervals automatically
select only the coordinates of that parity.

Here are the only missing chosen neighbors. At \(a\), the left
neighbor \((-1,0)\) is represented by
\((-1,0)+U=(2d-1,2)\), with correction \(9\). At
\((2-d,d)\), its left neighbor is represented by
\((1-d,d)+U=f\), with correction \(5\). All other chosen
neighbors lie in \(D\).

For exhaustiveness, the first seven rows handle the special cells,
the nonpositive half-plane, the bottom and top rows, and the lower
right shelf. Among the remaining even cells, \(t\le d\) is the
left region, \(t=d+2\) consists of the two endpoints and \(A_3\),
and \(t\ge d+4,\ x\le d\) is the middle region. For \(x\ge d+1\),
the spine \(x=d+1\) is \(A_2\); the remaining cells have
\(t\le2d\) or \(t=2d+2\). These are the last two rows.

### 7.4 Odd AND-cells: both vertical neighbors decrease

By (B5.9), neither neighbor of an odd AND-cell lies outside \(D\).
Odd cells on the bottom or top row, on the lower right shelf,
or on the outer diagonal \(t=2d+3\), are all OR. The special
cells \(e,f\) are OR as well. Thus the following four cases cover
all odd AND-cells.

* If \(x\le0\), the center correction is \(1\), and both vertical
  neighbors have correction \(0\). The only exceptional even
  correction with \(x\le0\) is at \(a\); an adjacent center in
  \(D\) would then be \((0,1)\), which is OR.
* In the left region, the center has
  \(\rho_D=8(d+1-x)+1\). A vertical neighbor normally has
  correction \(8(d+1-x)\); a neighbor on the bottom row has
  correction zero. The only possible AND-center on
  \(t=d+1\) in this region is \((1,d)\), since all the other
  positive-coordinate points of that diagonal are in \(Z_1\).
  Its upper neighbor is \((1,d+1)\), of correction \(8\),
  at most \(8(d+1-x)=8d\).
* In the middle region, the center has correction \(9\).
  The diagonal \(t=d+3\) is all OR, by \(Z_2\) and the exit
  cases. Hence an odd AND-center here satisfies \(t\ge d+5\).
  Both vertical neighbors have correction \(8\), including
  any neighbor on the top row; since \(x\le d\), neither
  can be one of the special points \(f,b\).
* In the right region, the center has
  \(\rho_D=8(2d-x)+1\), with \(x\le2d-1\).
  Its vertical neighbors normally have correction \(8(2d-x)\).
  A neighbor on the lower shelf, at the central endpoint
  \((d+1,1)\), or on \(t=2d+2\), has correction \(8\),
  which is at most \(8(2d-x)\). The special even point \(c\)
  would require a center of first coordinate \(2d\), impossible
  in this region.

In every case both neighbors have correction at most the center
correction minus one. Vertical motion leaves \(6x\) unchanged,
so both rank differences are negative.

### 7.5 Odd OR-cells: one vertical neighbor decreases

The union in (B5.9) has only two repetitions:
\[
B_-\cap Z_1=\{(d,1)\},\qquad
B_+\cap Z_2=\{(2,d+1)\}.
\]
There are no other intersections between its five component sets.
For example \(B_-\) has sums \(1\), the odd bottom coordinates,
or \(x+1\) on \(y=1\); intersecting with \(t=d+1\) gives only
\((d,1)\), while the \(y\)-range of \(Z_2\) excludes its lower
boundary. Reflection gives the corresponding upper intersection.
The two \(Z\)-diagonals and \(Z_3\) are mutually disjoint.
The following table therefore exhausts the odd OR-cells after the
two indicated repetitions are omitted from the \(Z\)-rows.

| Center | Chosen direction | Center correction | Chosen neighbor correction or representative |
|---|---|---:|---|
| \((x,1-x)\), \(2-d\le x\le-1\) | up | \(1\) | \(0\), inside \(D\) |
| \((x,0)\), odd \(1\le x\le d-1\) | down | \(1\) | \(0\) at representative \((x+1-d,d)\), using \(+V\) |
| \((d,1)\) | down | \(9\) | \(8\) at representative \((1,d+1)\), using \(+V\) |
| \((x,1)\), even \(d+2\le x\le2d-2\) | down | \(9\) | \(8\) at representative \((x+1-d,d+1)\), using \(+V\) |
| \(e=(2d,1)\) | up | \(5\) | \(4\) at \(c\) |
| \(t=2d+3,\ d+3\le x\le2d\) | up | \(1\) | \(0\) at representative \((x-2d,y-1)\), using \(-U\) |
| \((x,d+2)\), odd \(3\le x\le d-1\) | down | \(9\) | \(8\), inside \(D\) |
| \(f=(d+1,d+2)\) | up | \(5\) | \(4\) at representative \(c\), using \(-V\) |
| \((x,d+1)\), even \(2-d\le x\le0\) | down | \(1\) | \(0\), inside \(D\) |
| \((2,d+1)\) | up | \(9\) | \(8\) at representative \((d+1,1)\), using \(-V\) |
| \(Z_1\setminus\{(d,1)\}\) | down | \(8(d+1-x)+1\) | \(8(d+1-x)\), inside \(D\) |
| \(Z_2\setminus\{(2,d+1)\}\) | up | \(9\) | \(8\), inside \(D\) |
| \((0,1)\) | up | \(1\) | \(0\) at \((0,2)\) |
| \((d+2,d+1)\) | up | \(1\) | \(0\) at \(b\) |

The first five rows are \(B_-\). The next five are its reflected
set \(B_+\); the displayed directions need not be reflections of
the earlier choices. In each row the chosen neighbor's correction
is exactly one smaller, and the actual move is vertical. Thus its
rank is exactly one smaller.

### 7.6 Recurrence and verification

The covering and periodic consistency prove that the preceding rank
inequalities hold at every vertex of \(\mathbb Z^2\). Suppose a
nonempty finite forbidden set \(F\) existed. Choose a point of \(F\)
minimizing \(R\). If it is an AND-cell, forbiddenness supplies at
least one incoming neighbor in \(F\), but both incoming neighbors
have strictly smaller rank. If it is an OR-cell, forbiddenness
requires both incoming neighbors in \(F\), including the one of
strictly smaller rank selected above. Both cases contradict
minimality. Therefore no nonempty finite forbidden set exists;
BLUEPRINT L6(a), equivalently the rank criterion L9, proves recurrence.
This proves B5 L22 uniformly,
and the harmonic rotation proves B6 L22.

The tiny authorized independent check at \(d=4\) verified periodic
consistency and all 57 tile in-stars, with zero rank failures.
After the uniform proof was complete and the shared-machine memory
recovered, `scripts/base_b5_explicit_rank.py` independently checked
all 52 even parameters \(d=4,6,\ldots,100,128,200,502\). It checked
983658 tile in-stars, all overlap equalities of \(\rho\), and all
1463794 specified decreasing incoming edges, using the actual global
extension to decide whether the center is AND or OR. Every check
passed; the minimum rank drop was one for every parameter. The exact
output is `data/base_b5_rank_verification.json`. Both saved scripts
were run with `nice` and enforce `MemAvailable >= 34 GiB` immediately
before starting their parameter sweep.
