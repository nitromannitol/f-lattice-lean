# Base-family analysis (2026-10-20)

This file uses only the algorithm specification and the proved general lemmas, not the paper's proof. It is a proposed addition to BLUEPRINT §4.

## B1: L20, L21, L23 and L24 [PROVED]

Let `d >= 3` be odd, `T=d²+2d-1`, `v₁=(d,1)`, `v₂=(1-d,d+1)`, and `c₂=-d(d+3)/2`. Write

`Q(y)=-y(y-1)/2`, `F(x,y)=Q(y)+min(x-1,0)`.

The B1 domain is

`R={2-d <= x <= d, 0 <= y <= d+1, 1 <= x+y <= d+2}`

plus the two cells `a=(0,0)` and `b=(2,d+1)`. The tile equals `F` on `R` and `F+1` at `a,b`. Its parity bit is zero.

### L20/L23: complete compatibility and covering proof

The coordinate ranges on the domain are `2-d <= x <= d`, `0 <= y <= d+1`, and the level `s=x-dy` ranges from `1-T` to `d`. If two distinct domain cells differ by `v=A v₁+B v₂`, then `s(v)=-BT`; hence `|B|<=1` because the level range has width `T+d-1<2T`. If `B=0`, the x-coordinate range gives `|A|<=1`. If `B=1`, the y-coordinate bound on `v` gives `A<=0`, while the lower x-coordinate bound gives

`Ad+1-d >= -(2d-2)`, hence `Ad>=1-d`, hence `A>=0`.

Thus `A=0`. The case `B=-1` follows by negation. Consequently the only nonzero possible overlap vectors are `±v₁,±v₂`.

The higher endpoints `z` of pairs `z,z-v₁` in the domain are exactly

* `z=(x,y)` with `x+y=d+2` and `2<=x<=d`;
* `z=(d,1)`, whose lower endpoint is `a`;
* `z=b`, whose lower endpoint is `(2-d,d)`.

For the first set, `x>=2`, `x-d<=0`, and

`F(x,y)-F(x-d,y-1)=-(y-1)-(x-d-1)=d+2-x-y=0`.

For the second pair, both values are zero. For the third, both values are `-d(d+1)/2+1`. Thus compatibility holds for `v₁` with `c₁=0` on all `d+1` pairs.

The lower endpoints of pairs `z,z+v₂` are exactly `(j,0)` for `1<=j<=d`. Their upper endpoints are `(j+1-d,d+1)`, and

`o(j+1-d,d+1)-o(j,0)=-d(d+1)/2+j-d=j+c₂=s(j,0)+c₂`.

This checks all `d` pairs for `v₂`. The compatibility identities for the negative vectors follow by rearranging these identities and the cocycle formula. There are no other pairs to check.

There cannot be three distinct domain cells in one lattice class: their pairwise differences would be among `±v₁,±v₂`, but differences of two distinct such displacements from a common cell cannot again be in this list. Thus multiplicity is at most two. Count the rows of `R`: lengths `d,d+1`, then `d-2` rows of length `d+2`, then `d+1,d`. Together with `a,b` this gives `|D|=d²+4d`. There are exactly `(d+1)+d=2d+1` unordered repeated pairs, so the domain represents

`d²+4d-(2d+1)=T`

distinct lattice classes. Since the quotient has exactly `T` classes, it covers every class. This proves L20, with multiplicity exactly two on repeated classes, and L23. L13 now gives the integer periodic global extension `E` and its required growth.

### L21: exact Laplacian formula on the full tile

The formula is

`ΔE(x,y)=-1` exactly when either

* `x+y` is even and `x=1`; or
* `x+y` is odd, `0<y<d+1`, and `1<x+y<d+2`.

It is zero at every other domain cell. Here the first condition is understood on `D`; the relevant even cells are `(1,y)` for odd `1<=y<=d`.

Proof: away from domain exits and the two extra corners, the horizontal second difference of `F` is `-1` at `x=1` and zero elsewhere; its vertical second difference is always `-1`.

The horizontal in-neighbours outside the domain occur in exactly these four cases:

| centre | outside neighbour | representative in D | outside value minus F |
|---|---|---|---|
| `(0,0)` | `(-1,0)` | `(d-1,1)` via `+v₁` | `2` |
| `(d,1)` | `(d+1,1)` | `(1,0)` via `-v₁` | `0` |
| `(2-d,d)` | `(1-d,d)` | `(1,d+1)` via `+v₁` | `0` |
| `(2,d+1)` | `(3,d+1)` | `(3-d,d)` via `-v₁` | `2` |

These statements include `d=3`. They follow by inspecting the row intervals above and using that their nonexceptional diagonal endpoints have odd coordinate sum. The first and last centres have their own values `F+1`, so the correction `+2` at their outside neighbour cancels the centre correction `-2`; their Laplacian is zero. No other even centre has either corner as an in-neighbour. This proves the even part.

For odd centres, the vertical exits and special inside-neighbour corrections are exactly:

1. Bottom row `(x,0)`, odd `1<=x<=d`: the lower neighbour `z=(x,-1)` has representative `z+v₂=(x+1-d,d)`. The compatibility rule gives `E(z)=0=F(z)+1`.
2. Top row `(x,d+1)`, odd `2-d<=x<=1`: the upper neighbour `z=(x,d+2)` has representative `z-v₂=(x+d-1,1)`. Thus `E(z)=x-1+c₂=F(z)+1`.
3. Lower diagonal `x+y=1`, `1<=y<=d-1`: at `y=1` the lower neighbour is the extra corner `a`, with value `F+1`. For `2<=y<=d-1`, the lower neighbour `z=(1-y,y-1)` has representative `z+v₁=(d+1-y,y)`, giving `E(z)=Q(y)=F(z)+1`.
4. Upper diagonal `x+y=d+2`, `2<=y<=d`: at `y=d` the upper neighbour is the extra corner `b`, with value `F+1`. For `2<=y<=d-1`, the upper neighbour `z=(d+2-y,y+1)` has representative `z-v₁=(2-y,y)`, giving `E(z)=Q(y)+1-y=F(z)+1`.

These four lists are disjoint and exhaust odd domain cells failing the two strict interior inequalities, with their one corrected neighbour each. All other odd cells have both neighbours at their uncorrected formula values. Hence the odd Laplacian is zero on the four lists and `-1` elsewhere. Since the domain covers the quotient and the Laplacian is periodic, L21 follows globally.

### L24: central symmetry

Let `w=(2,d+1)`. The domain is invariant under `z -> w-z`, including the interchange of its extra corners. The parity of `w` is even. Direct calculation gives, on all domain cells,

`o(w-z)-o(z)=-s(z)+K`, where `K=1-d(d+1)/2`.

Indeed `Q(d+1-y)-Q(y)=dy-d(d+1)/2` and `min(1-x,0)-min(x-1,0)=1-x`; the extra corner corrections cancel. Define `H(z)=E(w-z)-E(z)+s(z)`. Its increment along `v₁` is zero. Its increment along `v₂` is

`-s(w)-2c₂-2T=0`.

Therefore `H` is lattice-periodic, and since it equals `K` on the covering domain it equals `K` everywhere. Applying the Laplacian to this affine identity proves `ΔE(w-z)=ΔE(z)` globally.

### Independent adversarial check [VERIFIED COMPUTATIONALLY]

`scripts/base_b1_research.py check` constructs the formula directly, separately from `spec_recursion.py`, and checks covering, multiplicity, every compatibility pair, the exact Laplacian formula, the affine symmetry identity, and off-domain symmetry samples. It passed for all odd `d` from `3` through `103` and for `d=127,201` (53 values; the previous general base checks only reached `k=8`). The script uses the existing exact quotient/extension arithmetic but does not use any value or domain routine from the algorithm port.

## B1 recurrence: initial unsuccessful narrow-strip attempt

The exact Laplacian description above is a substantially smaller recurrence problem. A naive two-column half-plane burn is insufficient: for `d=5` it burns 30 of the 34 first-column cells, leaving `(0,28),(0,29),(0,30),(0,31)` modulo vertical period 34. For `d=7` it leaves six first-column cells. Wider strips burn. This initial obstruction was subsequently overcome by the explicit rank below.

## B1 L22: explicit uniform recurrence rank [PROVED]

The recurrence gap for B1 is now closed. The earlier two-column experiment only obstructs that particular narrow certificate.

For `z=(x,y)` in `D`, put `p=(x+y) mod 2` and define the integer `ρ_D` by this ordered list (the first applicable clause wins):

1. `ρ_D=4` at `(0,0)` and `(d,1)`.
2. `ρ_D=5` at `(d,0)` and `(1,d+1)`.
3. `ρ_D=p` if `y=0`, `y=d+1`, or `x<=0`.
4. `ρ_D=8(d-x)+p` if `x>=1`, `1<=y<=d`, and `x+y<=d`.
5. `ρ_D=8` if `x+y=d+1`.
6. `ρ_D=1` if `x+y=d+2`.

These clauses cover `D`. Every overlap pair for `v₁` has equal values of `ρ_D`: the diagonal overlap has value 1 at both endpoints; the special pair `(d,1),(0,0)` has value 4; the special pair `(2,d+1),(2-d,d)` has value 0. On each `v₂` overlap, the lower point `(j,0)` and upper point `(j+1-d,d+1)` both have value `j mod 2` for `j<d`, and both have value 5 for `j=d`. Thus `ρ_D` defines a well-defined lattice-periodic integer function `ρ` on the whole plane. Define

`R(x,y)=6x+ρ(x,y)`.

For every AND-cell, **both** in-neighbours have smaller `R`; for every OR-cell, **at least one** in-neighbour has smaller `R`. The following exhaustive symbolic verification proves this; it uses only `d>=3` odd and the already proved Laplacian formula. Whenever a neighbour lies outside `D`, its representative is specified.

### Even AND-cells

They are exactly `(1,y)` for odd `1<=y<=d`.

* If `y<d`, the centre has `ρ=8(d-1)`. The left neighbour has `ρ=1`, so its rank minus the centre rank is `-6+1-8(d-1)<0`. The right neighbour has `ρ=8(d-2)+1`, so its rank minus the centre rank is `6+8(d-2)+1-8(d-1)=-1`.
* If `y=d`, the centre has `ρ=8`. Both neighbours have `ρ=1`; their rank differences are `-13` and `-1`.

### Even OR-cells

The following disjoint classes cover all even cells other than the spine above.

* `a=(0,0)`: choose left. Its outside neighbour `(-1,0)` is represented by `(d-1,1)`, whose `ρ=9`; the rank difference is `-6+9-4=-1`.
* `(d,1)`: choose left. The neighbour `(d-1,1)` has `ρ=9`; again the difference is `-1`.
* `b=(2,d+1)`: choose left, at `(1,d+1)` with `ρ=5`; the difference is `-6+5-0=-1`.
* All other even cells with `x<=0`: choose left. The centre has `ρ=0`. A neighbour inside `D` has `ρ=1`; the only possible outside neighbour in this class is `(1-d,d)` from centre `(2-d,d)`, represented by `(1,d+1)` with `ρ=5`. Thus the rank difference is either `-5` or `-1`.
* Bottom-row even cells `(x,0)` with `2<=x<=d-1`: choose left. The neighbour has `ρ=1`, the centre has `ρ=0`, and the difference is `-5`.
* Interior even cells with `x>=2` and `x+y<=d`: since `d` is odd, actually `x+y<=d-1`. Choose right, whose `ρ=8(d-x-1)+1`; the centre has `ρ=8(d-x)`. The difference is `-1`.
* Interior even cells with `x>=2` and `x+y=d+1`, excluding `(d,1)`: choose right. The neighbour is an upper-diagonal odd cell of `ρ=1`; the centre has `ρ=8`, giving difference `-1`.

There are no further top-row even cells with `x>0` except `b`, and no even cells on `x+y=d+2` since that sum is odd. This completes the even verification.

### Odd AND-cells

They obey `0<y<d+1`, `1<x+y<d+2`; since their sum is odd, `3<=x+y<=d`.

* If `x<=0`, the centre has `ρ=1`. Both vertical neighbours have `ρ=0`. The exceptional corner `a` cannot be a neighbour because that would make the centre `(0,1)`, whose sum is 1 and which is OR. Thus both rank differences are `-1`.
* If `x>=1`, the centre has `ρ=8(d-x)+1`. Each vertical neighbour is either a generic interior even cell of `ρ=8(d-x)`, a bottom-row even cell of `ρ=0`, or an upper adjacent-diagonal even cell of `ρ=8`. In the last case the centre has sum `d`, so `x<=d-1` and `8<=8(d-x)`. The exceptional `(d,1)` is not such a neighbour: it would force a centre on the bottom row or on sum `d+2`. No top-row neighbour is possible with `x>=1` for an odd AND-cell. Hence both neighbours have `ρ<=8(d-x)`, and both rank differences are at most `-1`.

### Odd OR-cells

These are exactly the four boundary lists used in the Laplacian proof.

* Bottom row, odd `1<=x<d`: choose down. The outside neighbour `(x,-1)` is represented by `(x+1-d,d)`, with `ρ=0`; the centre has `ρ=1`.
* Bottom endpoint `(d,0)`: choose up to `(d,1)`; `ρ` drops from 5 to 4.
* Top row, odd `2-d<=x<1`: choose down; `ρ` drops from 1 to 0.
* Top endpoint `(1,d+1)`: choose up. The outside neighbour `(1,d+2)` is represented by `(d,1)` via `-v₂`; `ρ` drops from 5 to 4.
* Lower diagonal `x+y=1`, `1<=y<=d-1`: choose up; the centre has `ρ=1` and its inside neighbour at sum 2 has `ρ=0`.
* Upper diagonal `x+y=d+2`, `2<=y<d`: choose up. The outside neighbour has representative `(2-y,y)` via `-v₁`, with `ρ=0`; the centre has `ρ=1`.
* Upper endpoint `(2,d)`: choose up to `b`, dropping `ρ` from 1 to 0.

All these moves are vertical, so rank drops by exactly one. The lists are disjoint and exhaustive.

Since translation by a lattice vector changes `R` by a constant, the inequalities verified on the covering domain hold globally. Choose both lower-rank neighbours at AND-cells, and one of the displayed lower-rank neighbours at OR-cells. A finite directed cycle of dependency edges would strictly decrease the integer `R` around the cycle, which is impossible. Lemma L9(a), equivalently the forbidden-set argument, proves recurrence. This is a direct rank proof and does not invoke the false general implication from periodic acyclicity to a prescribed drift.

### Independent verification

`scripts/base_b1_explicit_rank.py` checks every overlap equality and every rank inequality directly against the global exact extension for the same 53 odd values `3<=d<=103`, `d=127,201`. All 256113 tile in-stars passed. The inequalities above constitute the uniform proof; the computation is an independent check, including the minimum parameter `d=3`, all four exceptional points, and boundary exits.

## Result after the first family

All of L20–L24 hold uniformly for B1. A separately proved harmonic quarter-turn conjugacy transports these properties to B2. The next section completes B3 as well.

## B3: reduction to B1 and complete L20–L24 proof [PROVED]

Let `d>=3` be odd and retain the B1 function `E₁`, `T`, and lattice. Set

`F₃(x,y)=-y(y+1)/2+min(0,2-x)+min(0,d-2+x)+max(x+y-2,0)`.

Let `H` be the lattice-periodic indicator of the `d-1` level classes

`h_j=2-(d+1)j (mod T)`, `1<=j<=d-1`,

and define the global integer function

`G(z)=E₁(z-e₁)+H(z)`.

### Compatibility and covering

On the B3 domain, `3-T<=s(z)<=d`. Each `h_j` lies in this interval, while `h_j+T>d` and `h_j-T<3-T`. Thus `H(z)=1` precisely when `s(z)=h_j` for one `j`. Solutions have the form

`z=(2-j,j)+a(d,1)`.

Within the B3 domain only `a=0` occurs, except for `a=-1,j=1`, giving `c=(1-d,0)`, and `a=1,j=d-1`, giving `c'=(3,d)`. To see completeness, the sum `x+y` at these points is `2+a(d+1)`; `|a|>=2` lies beyond the full domain's sum range `[-d,d+4]`. For `a=-1` the sum is `1-d`, below the main region's lower bound, and the only listed extra cell of that sum on these orbits is `c`; for `a=1` the sum is `d+3`, above the main region's upper bound, and only `c'` qualifies. Hence the `H=1` cells are the internal `+1` diagonal and these two corners.

For a main-region point with `x+y>=2`, use the B1 representative `(x-1,y)`. It is in B1 except at `(x,y)=(2-d,d)`; there use `(1,d+1)` after adding `v₁`. Since `x+y>=2` implies `x>=2-d`, the two minima simplify to

`F₃(x,y)=Q(y)+min(x-2,0)=F₁(x-1,y)`.

At the exceptional point, direct substitution gives the same B1 value through `(1,d+1)`.

For a main-region point with `x+y<=2`, use `(x+d-1,y+1)`, which differs from `(x-1,y)` by `v₁`. It is in B1 except at `(2,0)`, where `(1,0)` is used instead. Here

`F₃(x,y)=-y(y+1)/2+min(x+d-2,0)=F₁(x+d-1,y+1)`.

For the bottom extra strip `(x,-1)`, `1-d<=x<=0`, use `(x+d-1,0)` in B1; its left endpoint maps to the B1 extra corner `(0,0)`, accounting for the bottom-strip corner correction. For the top extra strip `(x,d+1)`, `4-d<=x<=3`, use `(x-1,d+1)`; its right endpoint maps to the B1 extra corner `(2,d+1)`. At the two remaining extra corners `c,c'`, use `(0,1)` and `(2,d)` respectively; the B3 extra `+1` is precisely `H`. These checks prove `G=o_B3` everywhere on its domain.

Because `E₁(z-e₁)` has constants `c₁=0`, `c₂=-d(d+3)/2-1`, and `H` is lattice-periodic, `G` has exactly the B3 constants. Thus compatibility holds automatically on every overlap.

For covering, start with the covering domain `D_B1+e₁`. Every point lies in B3 except the following boundary pieces, whose indicated equivalent representative belongs to B3:

* `(d+1,0)` maps by `-v₁+v₂` to `(2-d,d)`;
* `(d+1,1)` maps by `-v₁` to `(1,0)`;
* all points with `x+y=d+3` map by `-v₁` to the diagonal `x+y=2` (including `(d+1,2)`);
* `(3-d,d+1)` maps by `-v₂` to `(2,0)`.

The extra B1 corners after translation, `(1,0)` and `(3,d+1)`, are already in B3. This proves covering.

For the table's counts, the main-region row lengths are `2d-1,2d`, then `d-3` rows of length `2d+1`, then `2d,2d-1`. Adding two strips of `d` cells and the two extra corners gives `2d²+5d-3` cells. For a fixed level there are at most two representatives: three would include a pair differing by `2v₁`; the main-region sum width is only `2d`, while `s` is fixed and a `2v₁` displacement changes the sum by `2d+2`. Inspection of the possible extra-strip endpoints rules this pair out: at the low end the translated x-coordinate exceeds `d`, and at the high end the inverse-translated x-coordinate is below `4-2d`. A lattice class has at most two levels, since the full level range has width `T+d-3<2T`. Hence multiplicity is at most four. It is exactly four, for example for every level residue `3<=s<=d`, represented by

`(s-d,-1), (s,0), (s-2d+1,d), (s-d+1,d+1)`.

This proves L20 and L23 in full, including the table counts.

### Symmetry (also used to shorten the boundary calculation)

Set `w=(4-d,d)`, an even vector. The domain and all its correction cells are invariant under `z -> w-z`. On the whole plane, the elementary min/max identities give

`F₃(w-z)-F₃(z)=-s(z)+2-d(d+1)/2`.

Indeed the two x-minima exchange, and `max(2-u,0)-max(u-2,0)=2-u` for `u=x+y`. Therefore the same affine identity holds for the tile. As in B1, the periodicity constants satisfy `-s(w)-2c₂-2T=0`, so the affine identity extends globally. This proves L24, and also shows that the collar correction `G-F₃` is invariant under this reflection.

### Exact Laplacian formula

For an **even** domain cell, `ΔG=-1` exactly at

* `1<=y<=d-1` and one of `x=2-d`, `x=2`, `x+y=2`;
* the two corners `(1-d,0),(3,d)`.

For an **odd** domain cell, `ΔG=0` exactly on the following lists, and it is `-1` elsewhere:

* the bottom and top strips `y=-1,d+1`;
* `y=0,x>=1`, or `y=d,x<=3-d`;
* `x+y=2-d, 1<=y<=d-2`;
* `x+y=d+2, 2<=y<=d-1`;
* `x+y=1, 0<=y<=d-2`;
* `x+y=3, 2<=y<=d`.

Here and below all conditions are restricted to the domain. A complete boundary verification follows. Write the tile as `F₃+δ`, where `δ=1` on the internal diagonal and four stated corner cells, and zero elsewhere. The horizontal second difference of `F₃` is

`-[x=2]-[x=2-d]+[x+y=2]`,

and its vertical second difference at odd cells is `-1`. The following are all exits on the lower/left half of the boundary; their reflections in `w` are all the remaining exits. Each row gives the centre, outside in-neighbour `z`, and `G(z)-F₃(z)`.

| centre | outside neighbour | correction |
|---|---|---|
| `(4-2d,d-1)` | `(3-2d,d-1)` | 0 |
| `(1-d,0)` | `(-d,0)` | 1 |
| `(2-d-y,y)`, `2<=y<=d-2` | `(2-d-y,y-1)` | 1 |
| `(1,0)` | `(1,-1)` | 0 |
| `(x,0)`, odd `3<=x<=d` | `(x,-1)` | 1 |
| `(x,-1)`, even `3-d<=x<=0` | `(x,-2)` | 1 |
| `(1-d,-1)` | `(1-d,-2)` | 2 |

The bounds are empty when appropriate, including `d=3`. These corrections follow from `G=E₁(.-e₁)+H` by the following explicit B1 representatives for `z-e₁`, in the same row order:

`(2-d,d)`, ` (d-1,2)`, `(1-y,y)`, `(1,d+1)`, `(x-d,d)`, `(x,d)`, `(1,d+1)`.

The corresponding lattice shifts are respectively `+v₁`, `+2v₁`, `+v₁`, `+v₁+v₂`, `+v₂`, `+v₁+v₂`, `+2v₁+v₂`. In the third row `H(z)=1` and in all other rows `H(z)=0`. Substituting the B1 formula and cocycle gives the displayed correction, so the table is a finite list of polynomial identities. For example the third row gives `E₁(z-e₁)=-y(y+1)/2=F₃(z)`, with the additional `H(z)=1`; the two last rows give `E₁(z-e₁)=0`, whereas `F₃(z)=-1,-2`.

Now combine the generic second differences with these exit corrections and the inside values `δ`. At an even internal diagonal cell the generic `+1` and centre correction `-2` give `-1`; the two vertical kink lines give `-1`, except at their endpoints where the diagonal kink or a strip corner adds `+1`. At `(1-d,0)` and its reflection the outside correction `+1` and centre correction `-2` give `-1`. All remaining even cells have zero Laplacian. At odd cells adjacent to the internal correction line, the neighbour correction is `+1` precisely on the two inner-diagonal lists. At the outer-diagonal endpoints the neighbour is an even corner of `δ=1`; at the other outer-diagonal cells the exit correction is `+1`. The bottom/top row lists and noncorner strip cells receive their `+1` from the table, except `(1,0)` and its reflection, where it comes from the adjacent internal correction line. At each odd strip corner the generic `-1`, centre correction `-2`, adjacent even-corner correction `+1`, and outside correction `+2` sum to zero. There are no other correction incidences. This proves exactly the formula stated above, hence L21 globally.

### Uniform recurrence rank

On the B3 domain, let `p=(x+y) mod 2`. Define `ρ_D` by the following ordered clauses:

1. `ρ_D=8d` at `(1-d,0)` and `(1,1)`.
2. `ρ_D=8d-12` at `(3,d)`.
3. `ρ_D=8y-4` when `x+y=2` and `2<=y<=d-1`.
4. `ρ_D=8(1-x)+p` when `0<=y<=d-1`, `2-d<=x<=0`, and `x+y<=1` (the left high region).
5. `ρ_D=8(d+1-x)+p` when `1<=y<=d` and `x>=2` (the right high region).
6. `ρ_D=p` elsewhere.

The exhaustive overlap proof in the following completion subsection shows that this descends to lattice classes. Its proof uses the fact that each class is a single `v₁` pair or a four-point `v₁,v₂` rectangle and checks the complete overlap list.

Put `R=6x+ρ`. The rank inequalities have the following exhaustive verification.

* Even AND-cells: at `(1-d,0)` the left/right effective neighbour heights (subtracting `6x` at the centre) are `3,8d-1`, below `8d`; at `(3,d)` they are `8d-13,7`, below `8d-12` for `d>=3`. On either vertical kink spine the centre height is `8(d-1)`, and the two effective neighbour heights are `-5` and `8(d-1)-1`. At `(1,1)` they are `3,8d-1`, below `8d`. On the remaining correction diagonal the centre is `8y-4`, the left effective height is `8y-5`, and the right is `7`; both are smaller since `y>=2`.
* Even OR-cells in either high region choose the right neighbour: its effective height is exactly the centre height minus 1. At the right boundary `(d,1)`, the outside neighbour is represented by `(1,0)`, of height 1, and the same difference holds. Every remaining even OR-cell has height 0 and chooses left, at a class of height 1, giving rank difference `-5`. The only left exit in this class is from `(4-2d,d-1)`, whose neighbour is represented by `(3-d,d)` of height 1.
* Odd AND-cells in the left high region have centre height `8(1-x)+1`; both vertical neighbours have height at most `8(1-x)`. The only possible transition to the correction diagonal from this region would be an odd cell on sum 1 with `y<=d-2`, which is OR; the remaining sum-1 endpoint has an upper neighbour of height 0. Odd AND-cells in the right high region similarly have centre height `8(d+1-x)+1`, and both neighbours are at most `8(d+1-x)`; a neighbour at the exceptional corner `(3,d)` would make the centre an outer-diagonal OR-cell. For odd AND-cells of default height 1, both neighbours have default height 0: adjacency to a high region outside that region forces a strip/bottom/top OR-cell, and adjacency to a correction-line or exceptional even corner forces one of the listed OR diagonals. Thus all AND-neighbour inequalities hold.
* Odd OR-cells in the left high region (sum 1) choose down, decreasing `ρ` by 1. Odd OR-cells in the right high region (outer upper diagonal) also choose down, decreasing by 1. For the remaining default-height OR-cells, a height-0 neighbour is as follows: bottom strip and bottom row choose down; the outside representatives are `(x+1,d)` via `v₁+v₂` for a strip point `(x,-1)`, and `(x+1-d,d)` via `v₂` for a bottom-row point `(x,0)`. Top strip points with `x<=1` choose down, while its endpoint `(3,d+1)` chooses up, represented by `(2,0)` via `-v₁-v₂`. Top-row points with `x<=1-d` choose down; `(3-d,d)` chooses up, represented by `(2,0)` via `-v₂`. The outer lower diagonal chooses up inside the domain. The inner sum-3 diagonal chooses up inside the domain, except its endpoint `(3-d,d)`, already handled. Every displayed move lowers the rank by 1.

Together with the class-consistency proof below, this explicit rank proves B3 recurrence by L9.

### Independent exact checks

`scripts/base_b3_explicit_rank.py` independently verifies the complete Laplacian formula, all rank overlap equalities, and all rank inequalities on 502974 in-stars for the same 53 odd parameters through `d=201`. The uniform overlap proof is given next.

### Completion of B3 rank class consistency [PROVED]

This closes the sole qualification in the preceding subsection; B3 L22 is now unconditional.

First make the fixed-level multiplicity argument fully explicit. A pair `z,z+2v₁` in D would have lower coordinate sum in `[-d,2-d]`, so its sum is one of `-d,1-d,2-d`. At sum `-d` only the bottom corner `(1-d,-1)` occurs, and adding `2v₁` gives x-coordinate `d+1>d`. At sum `1-d` the only points are `(2-d,-1)` and `(1-d,0)`; adding `2v₁` again gives x-coordinate greater than d. At sum `2-d`, the upper point would have sum `d+4`, forcing it to be `(3,d+1)`; its inverse image `(3-2d,d-1)` is outside D. Larger multiples are excluded by the full sum width `2d+4<3(d+1)`. Hence a fixed level contains at most two representatives, differing by `v₁`.

If a lattice class contains two distinct levels, they must be `s` and `s-T` with `3<=s<=d`. The four representatives displayed above all exist; since multiplicity is at most four, they are all the representatives. Their `v₁,v₂` adjacency graph is a rectangle. A class containing one level has one representative or two joined by `v₁`. It therefore suffices to check rank equality on `v₁,v₂` overlaps.

The complete `v₂` overlap list, given by the lower endpoints, is

* `(x,0)`, `3<=x<=d`;
* `(x,-1)`, `3-d<=x<=0`.

Both endpoints in each pair have default value `p`, and `v₂` preserves parity.

For `v₁`, write the lower endpoint as `(x,y)`. The full overlap list is partitioned as follows:

1. `y=-1`, `1-d<=x<=0`. Both the bottom-strip point and its image `(x+d,0)` have default value `p`.
2. `y=0`, `1-d<=x<=0`. At `x=1-d` the two endpoints are the exceptions `(1-d,0),(1,1)`, both of value `8d`. For `2-d<=x<=0`, the lower endpoint has left-high value `8(1-x)+p`, and the upper endpoint has right-high value `8(d+1-(x+d))+p`, the same number.
3. `1<=y<=d-1`, both endpoints in the main region. Here necessarily `x<=0` and `x+y<=1`. If `x>=2-d`, the two values are the same left-high/right-high expressions as in item 2. If `x<=1-d`, the lower point lies left of the left-high region, and the upper point has `x+d<=1` and coordinate sum at least 3; both are default `p`.
4. The exceptional pair `(3-d,d-1)` and `(3,d)`. Both values are `8d-12`.
5. `y=d`, `4-2d<=x<=3-d`. Both the lower main-region point and upper top-strip point have default `p`.

The row intervals of the B3 domain show that these are exhaustive: the target y-coordinate is one larger; rows -1,0,d produce items 1,2,5; in the middle rows a main-region target forces the source sum at most 1, except for the sole extra target `(3,d)`. This proves all rank overlap equalities, uniformly in d.

**Final status of this file:** complete uniform proofs of L20–L24 for B1 and B3. Together with the harmonic rotation, these settle B2 and B4 as well. All supporting exact tests passed through the stated adversarial ranges.
