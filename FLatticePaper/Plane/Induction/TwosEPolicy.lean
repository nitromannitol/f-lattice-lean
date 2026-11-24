import FLatticePaper.Graph

noncomputable section

/-! The signed policy `e(-1,η)` of the twos words, as definitions on the twos tile (task 72).

The selection is the archive's pure-2 policy (`.work/fields/canonical/pure2_initialization/uniform_bulk.py`: `native`,
`candidate`; `rawall.py`: `free`; `check_flat_rank_formula.py`: the H/V classes), with the parameter `a = 2k+4`, so the word is
`2^(k+1)`, the tile is `paperNearLadderTile (2k+4)`, and the period vectors are `U = (a+1, a-1)` (`= (d, n)`, `d = 2k+5`,
`n = 2k+3`) and `V = (-2, 2a)`. The native domain uses the coordinates `(x, Y)` with `Y = y + 1`.

Numerical check of these definitions (`scripts/twos_signed_e.py`, `scripts/twos_archive_rank.py`, K = k+1 = 1..4): every
non-free white class has its candidate guard at its native copy (no mismatch), the free classes are the H/V classes, and
the selected inputs satisfy quota, the prices, the square clauses and the prescription at both signs. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper
open scoped Classical

/-- The archive's native fundamental domain (`uniform_bulk.py` `native`) in the coordinates `(x, y + 1)`: a box with the
strips `x = -1, Y ≤ a+1` and `x = a+1, Y ≥ 2a-1` removed, and the corners `(-1, 2a+1)` and `(a+1, a-1)` added. -/
def NativeT (a x y : ℤ) : Prop :=
  ((-1 ≤ x ∧ x ≤ a + 1 ∧ 1 ≤ y + 1 ∧ y + 1 ≤ 3 * a - 1 ∧ -1 ≤ y + 1 - x ∧ y + 1 - x ≤ 2 * a + 1) ∧
      ¬((x = -1 ∧ y + 1 ≤ a + 1) ∨ (x = a + 1 ∧ 2 * a - 1 ≤ y + 1))) ∨
    (x = -1 ∧ y + 1 = 2 * a + 1) ∨ (x = a + 1 ∧ y + 1 = a - 1)

/-- The low band of the candidate guard (`uniform_bulk.py` `candidate`, `low`). -/
def CandLow (a x y : ℤ) : Prop :=
  (y - x) % 2 = 1 ∧ -1 ≤ y - x ∧ y - x ≤ a - 3 ∧ 1 ≤ x ∧ x ≤ a ∧ y ≠ a - 1 ∧ ¬(y - x = -1 ∧ x = 1)

/-- The high band of the candidate guard (`uniform_bulk.py` `candidate`, `high`). -/
def CandHigh (a x y : ℤ) : Prop :=
  (y - x) % 2 = 1 ∧ a + 1 ≤ y - x ∧ y - x ≤ 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 1 ∧ y ≠ 2 * a - 1 ∧
    ¬(y - x = 2 * a - 1 ∧ x = a - 1)

/-- The east diagonal of the candidate guard. -/
def CandE (a x y : ℤ) : Prop := y - x = a - 2 ∧ 2 ≤ x ∧ x ≤ a

/-- The west diagonal of the candidate guard. -/
def CandW (a x y : ℤ) : Prop := y - x = a ∧ 0 ≤ x ∧ x ≤ a - 2

/-- The candidate guard: the white classes that the candidate displacement covers. -/
def CandGuard (a x y : ℤ) : Prop := CandLow a x y ∨ CandHigh a x y ∨ CandE a x y ∨ CandW a x y

/-- The candidate displacement (`uniform_bulk.py` `candidate`): east on `E`, west on `W`; on the bands, vertical `-1` below the
band's middle row and `+1` above it. -/
def candDisp (a x y : ℤ) : Site :=
  ((if CandE a x y then 1 else if CandW a x y then -1 else 0),
    (if CandLow a x y ∨ CandHigh a x y then
      (if y < (if CandLow a x y then a - 1 else 2 * a - 1) then -1 else 1)
    else 0))

/-- The H classes (`globalrank.py` `HV`): `(1,0)`, `(i, i-2)` for `2 ≤ i ≤ a`, and `(a+1, a-2)`. -/
def FreeHSite (a x y : ℤ) : Prop :=
  (x = 1 ∧ y = 0) ∨ (2 ≤ x ∧ x ≤ a ∧ y = x - 2) ∨ (x = a + 1 ∧ y = a - 2)

/-- The V classes (`globalrank.py` `HV`): `(0, j)` for `0 ≤ j < a` and `(-1, j)` for `a ≤ j < 2a`. -/
def FreeVSite (a x y : ℤ) : Prop :=
  (x = 0 ∧ 0 ≤ y ∧ y < a) ∨ (x = -1 ∧ a ≤ y ∧ y < 2 * a)

/-- The free classes: the H and V classes. -/
def FreeSite (a x y : ℤ) : Prop := FreeHSite a x y ∨ FreeVSite a x y

/-- The free tables (`check_flat_rank_formula.py`): on `H_0 = (1,0)` the input `(0,-η)`; on the other H classes east on even
sites and north on odd sites; on `V_0 = (0,0)` east; on the other V classes `(η,0)` on even sites and `(0,-η)` on odd sites. -/
def freeDisp (a η x y : ℤ) : Site :=
  if FreeHSite a x y then
    (if x = 1 ∧ y = 0 then (0, -η) else if EvenSite (x, y) then (1, 0) else (0, 1))
  else if x = 0 ∧ y = 0 then (1, 0)
  else if EvenSite (x, y) then (η, 0) else (0, -η)

/-- The alias translates of a site: `u = c - (i U + l V)` with `i, l ∈ {-1, 0, 1}` (`globalrank.py` `addresses`). -/
def AliasOf (a : ℤ) (c u : Site) : Prop :=
  ∃ i l : ℤ, (i = -1 ∨ i = 0 ∨ i = 1) ∧ (l = -1 ∨ l = 0 ∨ l = 1) ∧
    u = (c.1 - i * (a + 1) + 2 * l, c.2 - i * (a - 1) - 2 * a * l)

/-- A site is in a free class if one of its alias translates is an H or V site. -/
def FreeClass (a : ℤ) (c : Site) : Prop := ∃ u, AliasOf a c u ∧ FreeSite a u.1 u.2

/-- The selected inputs of the twos signed policy `e(-1,η)` at a centre `c` of the field `F`. Black centres keep both inputs.
A white centre keeps the free table at its free alias when its class is free; otherwise it keeps the candidate displacement at
its native copy (non-free white classes have a unique native copy, and the candidate guard holds there). -/
def TwosSel (a η : ℤ) (F : Field) (c i : Site) : Prop :=
  (laplacian F c = -1 ∧ Edge i c) ∨
  (laplacian F c = 0 ∧
    ((∃ u, AliasOf a c u ∧ FreeSite a u.1 u.2 ∧
        i = (c.1 + (freeDisp a η u.1 u.2).1, c.2 + (freeDisp a η u.1 u.2).2)) ∨
     (¬ FreeClass a c ∧ ∃ u, AliasOf a c u ∧ NativeT a u.1 u.2 ∧ CandGuard a u.1 u.2 ∧
        i = (c.1 + (candDisp a u.1 u.2).1, c.2 + (candDisp a u.1 u.2).2))))

/-- The period-lattice class key: `key c = (n c.1 - d c.2) mod T` with `n = a-1`, `d = a+1`, `T = 2a^2+4a-2`. -/
def classKey (a : ℤ) (c : Site) : ℤ := ((a - 1) * c.1 - (a + 1) * c.2) % (2 * a * a + 4 * a - 2)

/-- The closed tile: the native points, except the duplicated free copies `v + U` and `v + V` of native H/V sites (the copies
that are not H/V sites themselves). Checked against the computed tile, one site per class, for `a = 4, 6, 8, 10`
(`scripts/twos_tile_rank.py`). -/
def TwosTile (a : ℤ) (p : Site) : Prop :=
  NativeT a p.1 p.2 ∧
    ¬ ((∃ v : Site, FreeSite a v.1 v.2 ∧ NativeT a v.1 v.2 ∧
          (p = (v.1 + (a + 1), v.2 + (a - 1)) ∨ p = (v.1 - 2, v.2 + 2 * a))) ∧ ¬ FreeSite a p.1 p.2)

/-- The H-table value of the archive's `freer` (`globalrank.py`). -/
def freeH (a η x _y : ℤ) : ℤ :=
  let j := if x = 1 then 0 else x - 1
  if η = 1 then (if j = 0 then 2 * a + 1 else if j = a then 1 else 2 * (a + 1 - x))
  else (if j = 0 then 4 else if j = 1 then 1 else if j = a then 6 else 2 * a + 7 - 2 * x)

/-- The V-table value of the archive's `freer` (`globalrank.py`). -/
def freeV (a η _x y : ℤ) : ℤ :=
  let r := y - a
  if η = 1 then (if y < a then 2 * y - y % 2 else 2 * r + 1 + r % 2)
  else if y = 0 then 5
    else if y < a then 2 * a + 3 - 2 * y - y % 2
    else if y = a then 2
    else if y = a + 1 then 1
    else 2 * a + 4 - 2 * r + r % 2

/-- The bulk value of the archive (`globalrank.py` `bulkr`). -/
def bulkR (a η x y : ℤ) : ℤ :=
  let h := y - x
  let o := (x + y) % 2
  let cen := if h ≤ a - 2 then a - 1 else 2 * a - 1
  let off := if h ≤ a - 2 then 2 * a - 2 else 2 * a
  let dd := y - cen
  let r0 := off - 2 * (if dd < 0 then -dd else dd) - o
  let r := if η = -1 then (if y = cen + 1 then 1 - o else r0 + (if y < cen + 1 then 1 else 5)) else r0
  let first := if η = 1 then (if x = a then 2 * a - 3 else 2 * a + 1 - 2 * y)
    else (if x = 2 then 2 else 2 * a + 6 - 2 * y)
  let mid := if η = 1 then 2 * x + 3 else (if x = 1 then 2 * a else 2 * x + 4)
  if h = -1 then first else if h = a - 1 then mid else r

/-- The nine alias addresses of `(X, Y)` in the archive's order (`globalrank.py` `addresses`). -/
def aliasAddrs (a X Y : ℤ) : List Site :=
  [(0, 0), (0, -1), (0, 1), (-1, 0), (-1, -1), (-1, 1), (1, 0), (1, -1), (1, 1)].map
    (fun il => (X - il.1 * (a + 1) + 2 * il.2, Y - il.1 * (a - 1) - 2 * a * il.2))

/-- The first true guard's value, else the default (the archive's nested `If`). -/
def pickFirst : List (Prop × ℤ) → ℤ → ℤ
  | [], d => d
  | (g, v) :: rest, d => if g then v else pickFirst rest d

/-- The archive's `deckrank` at `(X, Y)`: the free offers of the nine addresses (in order), then the bulk offers. -/
def deckAt (a η X Y : ℤ) : ℤ :=
  let addrs := aliasAddrs a X Y
  pickFirst
    (addrs.flatMap (fun u => [(FreeHSite a u.1 u.2, freeH a η u.1 u.2), (FreeVSite a u.1 u.2, freeV a η u.1 u.2)]) ++
      addrs.map (fun u => (NativeT a u.1 u.2, bulkR a η u.1 u.2)))
    (-1000)

/-- A tile point of the class `k`. The tile has one point per class, so this is that point (`Classical.epsilon`). -/
def tilePoint (a k : ℤ) : Site := Classical.epsilon (fun p => TwosTile a p ∧ classKey a p = k)

/-- The deck-periodic rank: the archive's `deckrank` at the tile point of the class of `c`. It depends only on `classKey`, so it
is periodic under the period lattice. -/
def rhoTwos (a η : ℤ) (c : Site) : ℤ :=
  deckAt a η (tilePoint a (classKey a c)).1 (tilePoint a (classKey a c)).2

/-- Black centres (`laplacian = -1`) keep both incoming inputs. -/
theorem twosSel_black {a η : ℤ} {F : Field} {c i : Site} (h : laplacian F c = -1) :
    TwosSel a η F c i ↔ (i = incomingNeg c ∨ i = incomingPos c) := by
  simp [TwosSel, h, Edge]

/-- A white centre of a free class keeps only the free-table input of its free alias. -/
theorem twosSel_white_freeClass {a η : ℤ} {F : Field} {c i : Site} (h : laplacian F c = 0) (hf : FreeClass a c) :
    TwosSel a η F c i ↔
      ∃ u, AliasOf a c u ∧ FreeSite a u.1 u.2 ∧
        i = (c.1 + (freeDisp a η u.1 u.2).1, c.2 + (freeDisp a η u.1 u.2).2) := by
  simp [TwosSel, h, hf]

/-- Two free aliases of one site coincide: H and V sites are pairwise not translates by a period vector with coefficients in
`[-2, 2]` (the alias indices differ by at most two). -/
theorem freeAlias_unique {a : ℤ} (ha : 4 ≤ a) {c u u' : Site} (hu : AliasOf a c u) (hu' : AliasOf a c u')
    (hf : FreeSite a u.1 u.2) (hf' : FreeSite a u'.1 u'.2) : u = u' := by
  obtain ⟨i, l, hi, hl, rfl⟩ := hu
  obtain ⟨i', l', hi', hl', rfl⟩ := hu'
  rcases hi with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;>
    simp only [FreeSite, FreeHSite, FreeVSite, Prod.mk.injEq] at hf hf' ⊢ <;> omega

/-- A white centre of a free class keeps exactly one input. -/
theorem twosSel_white_freeClass_eq {a η : ℤ} (ha : 4 ≤ a) {F : Field} {c i i' : Site} (h : laplacian F c = 0)
    (hf : FreeClass a c) (hi : TwosSel a η F c i) (hi' : TwosSel a η F c i') : i = i' := by
  rw [twosSel_white_freeClass h hf] at hi hi'
  obtain ⟨u, hu, hfu, rfl⟩ := hi
  obtain ⟨u', hu', hfu', rfl⟩ := hi'
  have heq := freeAlias_unique ha hu hu' hfu hfu'
  subst heq
  rfl

end FLatticePaper.TwosEPolicy

end
