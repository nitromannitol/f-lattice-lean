import FLatticePaper.Tiles.SurgicalCorners
import FLatticePaper.Tiles.PartialBoundary
import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.BinaryWords
import FLatticePaper.Tiles.SiteStrings
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Affine factors along the boundary strings (surgical `lemma:weak_standard_odometer_properties` (b), in affine factors)

The printed identities of (b) are differences of affine factors. Each corner restriction is a translation of a base zero-,
one- or enlarged one-odometer (`PTFamily.odo`), and its affine factor is the `a` of that translation. Here the affine factor
of a placed tile of an odometer `S` is the slope of `S` on the tile minus the base slope of its type (`tileAffine`). It equals
the `a` of any `PTFamily` witness (`tileAffine_family`). Along a horizontal string the forward table makes the affine factor
constant (`chain_fwd`); along a reversed string the step is twice the base-slope change (`chain_rev`). -/

namespace FLatticePaper.Tiles

/-- The base slope of a placed zero-one tile type: the slope of its base odometer on its shape. -/
def zTileBaseSlope (z : ZTile) : ℚ × ℚ := slopeOf (zTileOdo z) (tileShape z)

/-- The affine factor of the restriction of `S` to the placed tile `t`: the slope of `S` on `t` minus the base slope. -/
def tileAffine (S : GInt → ℤ) (t : ZTile × GInt) : ℚ × ℚ :=
  slopeOf S (placedSites [t]) - zTileBaseSlope t.1

theorem zTileBaseSlope_zero : zTileBaseSlope .zero = (0, -1 / 2) := by
  norm_num [zTileBaseSlope, slopeOf, unitSquares, tileShape, zTileOdo, zeroOdometer]

theorem zTileBaseSlope_one : zTileBaseSlope .one = (1 / 2, -1 / 2) := by
  norm_num [zTileBaseSlope, slopeOf, unitSquares, tileShape, zTileOdo, oneOdometer]

theorem zTileBaseSlope_oneD : zTileBaseSlope .oneD = (1 / 2, -1 / 2) := by
  norm_num [zTileBaseSlope, slopeOf, unitSquares, tileShape, zTileOdo, oneOdometer]

theorem placedSites_single (t : ZTile × GInt) :
    placedSites [t] = (tileShape t.1).map (· + t.2) := by
  simp [placedSites]

theorem unitSquares_tileShape_ne (z : ZTile) : unitSquares (tileShape z) ≠ [] := by
  cases z <;> decide

theorem mem_of_mem_unitSquares {T : List GInt} {x : GInt} (h : x ∈ unitSquares T) :
    x ∈ T ∧ x + (1, 0) ∈ T ∧ x + (0, 1) ∈ T ∧ x + (1, 1) ∈ T := by
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2.1, h2.2.1, h2.2.2⟩

/-- The real square term of `slopeOf`. -/
def chainReTerm (f : GInt → ℤ) (x : GInt) : ℚ :=
  ((f (x + (1, 0)) : ℚ) - f x + ((f (x + (1, 1)) : ℚ) - f (x + (0, 1)))) / 2

/-- The imaginary square term of `slopeOf`. -/
def chainImTerm (f : GInt → ℤ) (x : GInt) : ℚ :=
  ((f (x + (0, 1)) : ℚ) - f x + ((f (x + (1, 1)) : ℚ) - f (x + (1, 0)))) / 2

theorem slopeOf_eq (f : GInt → ℤ) (T : List GInt) :
    slopeOf f T = (((unitSquares T).map (chainReTerm f)).sum / ((unitSquares T).length : ℚ),
      ((unitSquares T).map (chainImTerm f)).sum / ((unitSquares T).length : ℚ)) := rfl

/-- The slope depends only on the values on the tile. -/
theorem slopeOf_congr (f g : GInt → ℤ) (T : List GInt) (h : ∀ x ∈ T, f x = g x) :
    slopeOf f T = slopeOf g T := by
  have hsq : ∀ x ∈ unitSquares T, f x = g x ∧ f (x + (1, 0)) = g (x + (1, 0)) ∧
      f (x + (0, 1)) = g (x + (0, 1)) ∧ f (x + (1, 1)) = g (x + (1, 1)) := by
    intro x hx
    obtain ⟨h0, h1, h2, h3⟩ := mem_of_mem_unitSquares hx
    exact ⟨h x h0, h _ h1, h _ h2, h _ h3⟩
  rw [slopeOf_eq, slopeOf_eq]
  have hre : (unitSquares T).map (chainReTerm f) = (unitSquares T).map (chainReTerm g) := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨_, e1, e2, e3⟩ := hsq x hx
    unfold chainReTerm
    rw [e1, e2, e3, (hsq x hx).1]
  have him : (unitSquares T).map (chainImTerm f) = (unitSquares T).map (chainImTerm g) := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨_, e1, e2, e3⟩ := hsq x hx
    unfold chainImTerm
    rw [e1, e2, e3, (hsq x hx).1]
  rw [hre, him]

theorem chain_mem_map_add_iff (T : List GInt) (p y : GInt) : y ∈ T.map (· + p) ↔ y - p ∈ T := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    simpa using ha
  · intro h
    exact List.mem_map.mpr ⟨y - p, h, by simp⟩

theorem chain_unitSquares_map_add (T : List GInt) (p : GInt) :
    unitSquares (T.map (· + p)) = (unitSquares T).map (· + p) := by
  unfold unitSquares
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  have e : ∀ a : GInt, x + p + a - p = x + a := fun a => by abel
  simp only [Function.comp_apply, chain_mem_map_add_iff, e]

theorem chain_sum_map_add_const (S : List GInt) (f : GInt → ℚ) (c : ℚ) :
    (S.map fun x => f x + c).sum = (S.map f).sum + (S.length : ℚ) * c := by
  induction S with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    push_cast
    ring

theorem reTerm_translate (g : GInt → ℤ) (p a : GInt) (b : ℤ) (x : GInt) :
    chainReTerm (fun y => g (y - p) + a.1 * y.1 + a.2 * y.2 + b) (x + p) = chainReTerm g x + (a.1 : ℚ) := by
  unfold chainReTerm
  have h1 : x + p + (1, 0) - p = x + (1, 0) := by abel
  have h2 : x + p + (1, 1) - p = x + (1, 1) := by abel
  have h3 : x + p + (0, 1) - p = x + (0, 1) := by abel
  have h4 : x + p - p = x := by abel
  simp only [h1, h2, h3, h4, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem imTerm_translate (g : GInt → ℤ) (p a : GInt) (b : ℤ) (x : GInt) :
    chainImTerm (fun y => g (y - p) + a.1 * y.1 + a.2 * y.2 + b) (x + p) = chainImTerm g x + (a.2 : ℚ) := by
  unfold chainImTerm
  have h1 : x + p + (0, 1) - p = x + (0, 1) := by abel
  have h2 : x + p + (1, 1) - p = x + (1, 1) := by abel
  have h3 : x + p + (1, 0) - p = x + (1, 0) := by abel
  have h4 : x + p - p = x := by abel
  simp only [h1, h2, h3, h4, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- The slope of an affine translate of a base odometer is the base slope plus the affine factor. -/
theorem slopeOf_translate_affine (g : GInt → ℤ) (L : List GInt) (p a : GInt) (b : ℤ)
    (hne : unitSquares L ≠ []) :
    slopeOf (fun y => g (y - p) + a.1 * y.1 + a.2 * y.2 + b) (L.map (· + p)) =
      slopeOf g L + ((a.1 : ℚ), (a.2 : ℚ)) := by
  have hlen : ((unitSquares L).length : ℚ) ≠ 0 := by
    have : (unitSquares L).length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    exact_mod_cast this
  rw [slopeOf_eq, slopeOf_eq, chain_unitSquares_map_add, List.length_map, List.map_map, List.map_map]
  have hre : ((unitSquares L).map ((chainReTerm fun y => g (y - p) + a.1 * y.1 + a.2 * y.2 + b) ∘ (· + p))) =
      (unitSquares L).map (fun x => chainReTerm g x + (a.1 : ℚ)) :=
    List.map_congr_left fun x _ => reTerm_translate g p a b x
  have him : ((unitSquares L).map ((chainImTerm fun y => g (y - p) + a.1 * y.1 + a.2 * y.2 + b) ∘ (· + p))) =
      (unitSquares L).map (fun x => chainImTerm g x + (a.2 : ℚ)) :=
    List.map_congr_left fun x _ => imTerm_translate g p a b x
  rw [hre, him, chain_sum_map_add_const, chain_sum_map_add_const]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    field_simp
  · simp only [Prod.snd_add]
    field_simp

theorem tileSlope_eq (F : PTFamily) (S : GInt → ℤ) (k : ℕ) (hS : ∀ x ∈ F.dom k, S x = F.odo k x) :
    slopeOf S (placedSites [F.tile k]) = slopeOf (F.odo k) (F.dom k) := by
  have hdom : placedSites [F.tile k] = F.dom k := by
    rw [placedSites_single]
    rfl
  rw [hdom]
  exact slopeOf_congr S (F.odo k) (F.dom k) hS

/-- The affine factor of a placed tile of an odometer is the `a` of any family witness for it. -/
theorem tileAffine_family (F : PTFamily) (S : GInt → ℤ) (k : ℕ)
    (hS : ∀ x ∈ F.dom k, S x = F.odo k x) (hne : unitSquares (tileShape (F.tile k).1) ≠ []) :
    tileAffine S (F.tile k) = (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  have hT : F.dom k = (tileShape (F.tile k).1).map (· + (F.tile k).2) := rfl
  have hodo : F.odo k = fun y => zTileOdo (F.tile k).1 (y - (F.tile k).2) + (F.a k).1 * y.1 +
      (F.a k).2 * y.2 + F.b k := rfl
  unfold tileAffine
  rw [tileSlope_eq F S k hS, hodo, hT,
    slopeOf_translate_affine (zTileOdo (F.tile k).1) (tileShape (F.tile k).1) (F.tile k).2 (F.a k)
      (F.b k) hne]
  unfold zTileBaseSlope
  abel

/-- The forward table makes the affine factor constant along a horizontal string. -/
theorem table_fwd (z1 z2 : ZTile) :
    surgicalSlopeDiff .horizontal false (zTileLetter z1) (zTileLetter z2) =
      zTileBaseSlope z2 - zTileBaseSlope z1 := by
  cases z1 <;> cases z2 <;>
    simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one, zTileBaseSlope_oneD] <;>
    norm_num

/-- The reversed table: the step is the base-slope change of the first tile. -/
theorem table_rev (z1 z2 : ZTile) :
    surgicalSlopeDiff .horizontal true (zTileLetter z1) (zTileLetter z2) =
      zTileBaseSlope z1 - zTileBaseSlope z2 := by
  cases z1 <;> cases z2 <;>
    simp [surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one, zTileBaseSlope_oneD] <;>
    norm_num

/-- Along a forward horizontal string the affine factors are all equal to the first one. -/
theorem chain_fwd (F : PTFamily) (S : GInt → ℤ)
    (hS : ∀ k, k < F.n → ∀ x ∈ F.dom k, S x = F.odo k x)
    (hR : ∀ k, k + 1 < F.n → slopeOf (F.odo (k + 1)) (F.dom (k + 1)) - slopeOf (F.odo k) (F.dom k) =
      surgicalSlopeDiff .horizontal false (zTileLetter (F.tile k).1) (zTileLetter (F.tile (k + 1)).1)) :
    ∀ k, k < F.n → tileAffine S (F.tile k) = tileAffine S (F.tile 0) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have ihk : tileAffine S (F.tile k) = tileAffine S (F.tile 0) := ih (by omega)
    have hdiff := hR k hk
    rw [table_fwd] at hdiff
    have hstep : tileAffine S (F.tile (k + 1)) = tileAffine S (F.tile k) := by
      unfold tileAffine
      rw [tileSlope_eq F S (k + 1) (hS (k + 1) hk), tileSlope_eq F S k (hS k (by omega))]
      apply Prod.ext
      · have h1 := congrArg Prod.fst hdiff
        simp only [Prod.fst_sub] at h1 ⊢
        linarith
      · have h2 := congrArg Prod.snd hdiff
        simp only [Prod.snd_sub] at h2 ⊢
        linarith
    rw [hstep, ihk]

/-- Along a reversed horizontal string the quantity `a + 2 · base` is constant. -/
theorem chain_rev (F : PTFamily) (S : GInt → ℤ)
    (hS : ∀ k, k < F.n → ∀ x ∈ F.dom k, S x = F.odo k x)
    (hR : ∀ k, k + 1 < F.n → slopeOf (F.odo (k + 1)) (F.dom (k + 1)) - slopeOf (F.odo k) (F.dom k) =
      surgicalSlopeDiff .horizontal true (zTileLetter (F.tile k).1) (zTileLetter (F.tile (k + 1)).1)) :
    ∀ k, k < F.n → tileAffine S (F.tile k) + (zTileBaseSlope (F.tile k).1 + zTileBaseSlope (F.tile k).1) =
      tileAffine S (F.tile 0) + (zTileBaseSlope (F.tile 0).1 + zTileBaseSlope (F.tile 0).1) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hdiff := hR k hk
    rw [table_rev] at hdiff
    have hstep : tileAffine S (F.tile (k + 1)) + (zTileBaseSlope (F.tile (k + 1)).1 + zTileBaseSlope (F.tile (k + 1)).1) =
        tileAffine S (F.tile k) + (zTileBaseSlope (F.tile k).1 + zTileBaseSlope (F.tile k).1) := by
      unfold tileAffine
      rw [tileSlope_eq F S (k + 1) (hS (k + 1) hk), tileSlope_eq F S k (hS k (by omega))]
      apply Prod.ext
      · have h1 := congrArg Prod.fst hdiff
        simp only [Prod.fst_sub, Prod.fst_add] at h1 ⊢
        linarith
      · have h2 := congrArg Prod.snd hdiff
        simp only [Prod.snd_sub, Prod.snd_add] at h2 ⊢
        linarith
    rw [hstep, ihk]

/-! ### The corner identities in affine factors -/

theorem headD_eq_getD_zero' {α : Type*} (L : List α) (d : α) : L.headD d = L.getD 0 d := by
  cases L <;> rfl

theorem getLastD_eq_getD' {α : Type*} (L : List α) (d : α) :
    L.getLastD d = L.getD (L.length - 1) d := by
  simp [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem hRevStringAt_length (u : BinaryWord) (c : GInt) : (hRevStringAt u c).length = u.length := by
  unfold hRevStringAt
  simp only [List.length_zip, List.length_map, List.length_scanl, List.length_tail]
  omega

/-- The first coordinates of the reversed horizontal string are the letters of its word. -/
theorem hRevStringAt_map_fst (u : BinaryWord) (c : GInt) :
    (hRevStringAt u c).map Prod.fst = u.map letterZTile := by
  unfold hRevStringAt
  apply List.map_fst_zip
  simp only [List.length_map, List.length_scanl, List.length_zip, List.length_tail]
  omega

theorem hRevStringAt_getD_fst (u : BinaryWord) (c : GInt) (i : ℕ) (hi : i < u.length) :
    ((hRevStringAt u c).getD i (ZTile.zero, (0 : GInt))).1 = letterZTile (u.getD i .p) := by
  have e1 : ((hRevStringAt u c).map Prod.fst).getD i ZTile.zero =
      ((hRevStringAt u c).getD i (ZTile.zero, (0 : GInt))).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    generalize (hRevStringAt u c)[i]? = o
    cases o <;> simp
  have e2 : (u.map letterZTile).getD i ZTile.zero = letterZTile (u.getD i .p) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rw [← e1, hRevStringAt_map_fst, e2]

/-- The forward corner identity: the affine factors of the first and last tiles of the forward horizontal string agree.
No nonemptiness is needed: for the empty string the two tiles coincide. -/
theorem corner_fwd (wh : BinaryWord) (S : GInt → ℤ)
    (hR : RespectsTiles .horizontal false (hStringAt wh 0) S) :
    tileAffine S ((hStringAt wh 0).getLastD (ZTile.zero, 0)) =
      tileAffine S ((hStringAt wh 0).headD (ZTile.zero, 0)) := by
  obtain ⟨F, hF, hS, hRes⟩ := hR
  rw [getLastD_eq_getD', headD_eq_getD_zero', ← hF]
  rcases Nat.eq_zero_or_pos F.n with h0 | hpos
  · have hl : F.ts.length = 0 := h0
    simp [hl]
  · have key := chain_fwd F S hS (fun k hk => (hRes k hk).1) (F.n - 1) (by omega)
    exact key

/-- The reversed corner identity: for a reversed horizontal string whose first letter is `p` and last letter is `q`, the
affine factor of the last tile minus that of the first tile is `(-1, 0)`. -/
theorem corner_rev (u : BinaryWord) (c : GInt) (S : GInt → ℤ)
    (hhead : u.head? = some .p) (hlast : u.getLast? = some .q)
    (hR : RespectsTiles .horizontal true (hRevStringAt u c) S) :
    tileAffine S ((hRevStringAt u c).getLastD (ZTile.zero, 0)) -
      tileAffine S ((hRevStringAt u c).headD (ZTile.zero, 0)) = ((-1 : ℚ), (0 : ℚ)) := by
  have hu : u ≠ [] := by
    rintro rfl
    simp at hhead
  have h0 : u.getD 0 .p = .p := by
    cases u with
    | nil => exact absurd rfl hu
    | cons a l => simpa using hhead
  have hl : u.getD (u.length - 1) .p = .q := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hlast]
    rfl
  obtain ⟨F, hF, hS, hRes⟩ := hR
  have hn : F.n = u.length := by
    unfold PTFamily.n
    rw [hF, hRevStringAt_length]
  have hpos : 0 < u.length := List.length_pos_of_ne_nil hu
  have hF1 : ∀ i, F.tile i = (hRevStringAt u c).getD i (ZTile.zero, 0) := fun i => by
    rw [← hF]
    rfl
  have hfirst : (F.tile 0).1 = ZTile.zero := by
    rw [hF1, hRevStringAt_getD_fst u c 0 hpos, h0]
    rfl
  have hlast' : (F.tile (F.n - 1)).1 = ZTile.one := by
    rw [hF1, hRevStringAt_getD_fst u c (F.n - 1) (by omega), hn, hl]
    rfl
  have key := chain_rev F S hS (fun k hk => (hRes k hk).1) (F.n - 1) (by omega)
  rw [hlast', hfirst, zTileBaseSlope_one, zTileBaseSlope_zero] at key
  rw [getLastD_eq_getD', headD_eq_getD_zero', ← hF]
  show tileAffine S (F.tile (F.n - 1)) - tileAffine S (F.tile 0) = ((-1 : ℚ), (0 : ℚ))
  have h1 := congrArg Prod.fst key
  have h2 := congrArg Prod.snd key
  apply Prod.ext
  · simp only [Prod.fst_sub, Prod.fst_add] at h1 ⊢
    norm_num at h1 ⊢
    linarith
  · simp only [Prod.snd_sub, Prod.snd_add] at h2 ⊢
    norm_num at h2 ⊢
    linarith

/-- The head and last letters of the horizontal word of every standard tile, for both parities: the head is `q` and the last
letter is `p` (`almost_palindrome_two` at the empty prefix, whose parity is even). -/
theorem hWordOf_head_last (w : FLatticePaper.Farey.Word) (par : Bool) :
    (FLatticePaper.Tiles.SiteStrings.hWordOf w par).head? = some .q ∧
      (FLatticePaper.Tiles.SiteStrings.hWordOf w par).getLast? = some .p := by
  cases par
  · exact ⟨((almost_palindrome_two [] w).1 (by simp)).1, ((almost_palindrome_two [] w).1 (by simp)).2.1⟩
  · exact ⟨((almost_palindrome_two [] w).1 (by simp)).2.2.1, ((almost_palindrome_two [] w).1 (by simp)).2.2.2⟩

/-- The corner identities of (b) in affine factors (`lemma:weak_standard_odometer_properties` (b), with `c(T) = 0`), as printed:
`a_B - a_A = 0`, `a_C - a_D = a_{0/1,2} - a_{1/1,2} = (-1,0)`, `a_C - a_B = a_{n/d,2} - a_{1/1,2} = (n-1, 1-d)`, where `A,B`
are the first and last tiles of the forward horizontal string, and `C,D` the last and first of the reversed one. -/
def CornerAffineStatement (wh wv : BinaryWord) (n d : ℤ) (S : GInt → ℤ) : Prop :=
  tileAffine S (cornerTiles wh wv 0).2.1 - tileAffine S (cornerTiles wh wv 0).1 = 0 ∧
  tileAffine S (cornerTiles wh wv 0).2.2.1 - tileAffine S (cornerTiles wh wv 0).2.2.2 = ((-1 : ℚ), (0 : ℚ)) ∧
  tileAffine S (cornerTiles wh wv 0).2.2.1 - tileAffine S (cornerTiles wh wv 0).2.1 =
    (((n : ℚ) - 1), (1 - (d : ℚ)))

/-- The first two identities of (b) in affine factors, for a horizontal word with head `q` and last letter `p`. The third
identity is the target: it relates the last tile of the forward string to the last tile of the reversed one through the
vertical strings and the tile translation `v_{n/d,2}`. The third identity is proved for every weak standard family in
`SurgicalCornerThird` (`corner_3_family`, `corner_3_family_even`), from the respect conjuncts. -/
theorem corner_affine_12 (wh wv : BinaryWord) (S : GInt → ℤ)
    (hhead : wh.head? = some .q) (hlast : wh.getLast? = some .p)
    (hA : RespectsTiles .horizontal false (hStringAt wh 0) S)
    (hC : RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S) :
    tileAffine S (cornerTiles wh wv 0).2.1 - tileAffine S (cornerTiles wh wv 0).1 = 0 ∧
    tileAffine S (cornerTiles wh wv 0).2.2.1 - tileAffine S (cornerTiles wh wv 0).2.2.2 = ((-1 : ℚ), (0 : ℚ)) := by
  constructor
  · simp only [cornerTiles]
    rw [corner_fwd wh S hA, sub_self]
  · simp only [cornerTiles]
    have hu0 : wh.reverse.head? = some .p := by
      rw [List.head?_reverse]
      exact hlast
    have hul : wh.reverse.getLast? = some .q := by
      rw [List.getLast?_reverse]
      exact hhead
    exact corner_rev wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) S hu0 hul hC

/-- The first two identities of (b) for every odd child of a weak standard family, with no hypothesis on the word: the head
and last letters of its horizontal word are fixed (`hWordOf_head_last`), and the respect of its anchored strings is a conjunct
of the family. -/
theorem corner_12_family (S : FLatticePaper.Tiles.SurgicalWeak.WeakData) (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO)
    (w : FLatticePaper.Farey.Word) :
    tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).2.1 -
      tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).1 = 0 ∧
    tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).2.2.1 -
      tileAffine (oddO w).val (cornerTiles (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) 0).2.2.2 = ((-1 : ℚ), (0 : ℚ)) := by
  obtain ⟨_, hA, hC, _, _⟩ := (h w).2.2.2.2.1
  exact corner_affine_12 _ _ _ (hWordOf_head_last w false).1 (hWordOf_head_last w false).2 hA hC

end FLatticePaper.Tiles
