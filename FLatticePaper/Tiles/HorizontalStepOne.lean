import FLatticePaper.Tiles.TileTranslation
import FLatticePaper.Tiles.PTUniqueness
import FLatticePaper.Tiles.SurgicalAffineChain

/-! # The boundary-string formula of Step 1 for horizontal strings

Surgical edition 274ad18, Step 1 of `lemma:weak_standard_odometer_properties`: if partial odometers respect a horizontal (resp.
reversed horizontal) zero-one boundary string, then on every tile `T_i` of the string they are one fixed function of the tile
type, read at `x - c(T_i)`, plus one affine function and one constant for the whole string: `o_{type(i)}` for the forward string
and `ô_{type(i)}` for the reversed one (`o_i(x) - a_0^T x = o_{type(i)}(x - c(T_i)) + K`).

Here the fixed functions are `relOdo fwdStr` (the zero-one odometers `o_{0/1}`, `o_{1/1}`, `o^d_{1/1}`) and `relOdo revStr`
(in relative coordinates `ô_{0/1}(y) = o_{0/1}(y) + y_2 - 1`, `ô_{1/1}(y) = o_{1/1}(y) - y_1 + y_2`, the same for
`T^d_{1/1}`; `ô_{1/1}(1) = -1 = ô_{0/1}(0)`, the affine parts those of `HM`, `alphaH`, `cstH`). The explicit
family on the string (`famOf`) respects it, by the finite local checks of consecutive tiles (`pairOK_fwd`, `pairOK_rev`: the
table of single overlaps and the compatibility of non-overlapping neighbours) and the disjointness of non-consecutive tiles
(`triple_fwd`, `triple_rev`); any family respecting the same string is the explicit one plus one affine function
(`PTFamily.exists_affine_of_respects_gen`). The results are `horizontal_formula` and `reversed_horizontal_formula`, and the bottom
corner values of `eq:std_corner_values` (`bottom_corner_values`). -/

namespace FLatticePaper.Tiles.HorizontalStepOne

open FLatticePaper.Tiles

/-! ### The data of a horizontal string -/

/-- A horizontal string: the reversal flag of the slope table, the step between consecutive tiles by their letters, and the affine
factor and constant of the explicit family by tile type. -/
structure HStr where
  rev : Bool
  step : Letter → Letter → GInt
  alph : ZTile → GInt
  cst : ZTile → ℤ

/-- The forward horizontal string: steps `hOffset` of the second letter, the zero-one odometers. -/
def fwdStr : HStr := ⟨false, fun _ b => hOffset b, fun _ => 0, fun _ => 0⟩

/-- The reversed horizontal string: steps `hRevOffset`, the odometers `ô`. -/
def revStr : HStr :=
  ⟨true, hRevOffset, fun t => match t with | .zero => ((0 : ℤ), (1 : ℤ)) | _ => ((-1 : ℤ), (1 : ℤ)),
    fun t => match t with | .zero => -1 | _ => 0⟩

/-- The fixed function of a tile type in relative coordinates. -/
def relOdo (D : HStr) (t : ZTile) (y : GInt) : ℤ := zTileOdo t y + ptDot (D.alph t) y + D.cst t

/-- The tile type of a letter after `prev` (the rule of `tileSeqAux`). -/
def tileFor (prev : Option Letter) (x : Letter) : ZTile :=
  match x, prev with
  | .p, _ => ZTile.zero
  | .q, some .q => ZTile.oneD
  | .q, _ => ZTile.one

theorem zTileLetter_tileFor (prev : Option Letter) (x : Letter) : zTileLetter (tileFor prev x) = x := by
  cases x <;> rcases prev with _ | _ | _ <;> rfl

theorem tileSeqAux_cons (prev : Option Letter) (x : Letter) (xs : BinaryWord) :
    tileSeqAux prev (x :: xs) = tileFor prev x :: tileSeqAux (some x) xs := by
  cases x <;> rcases prev with _ | _ | _ <;> rfl

/-- The placed tiles of a string read after `prev`, from the position `c`. -/
def hAuxG (D : HStr) : Option Letter → BinaryWord → GInt → List (ZTile × GInt)
  | _, [], _ => []
  | prev, [a], c => [(tileFor prev a, c)]
  | prev, a :: b :: rest, c => (tileFor prev a, c) :: hAuxG D (some a) (b :: rest) (c + D.step a b)

theorem hStringAt_eq (w : BinaryWord) (c : GInt) : hStringAt w c = hAuxG fwdStr none w c := by
  have key : ∀ (prev : Option Letter) (w : BinaryWord) (c : GInt),
      (tileSeqAux prev w).zip (List.scanl (· + ·) c (w.tail.map hOffset)) = hAuxG fwdStr prev w c := by
    intro prev w
    induction w generalizing prev with
    | nil => intro c; rfl
    | cons a rest ih =>
      intro c
      cases rest with
      | nil => rfl
      | cons b rest' =>
        have := ih (some a) (c + hOffset b)
        rw [tileSeqAux_cons, List.tail_cons, List.map_cons, List.scanl_cons, List.zip_cons_cons]
        exact congrArg _ this
  exact key none w c

theorem hRevStringAt_eq (u : BinaryWord) (c : GInt) : hRevStringAt u c = hAuxG revStr none u c := by
  have key : ∀ (prev : Option Letter) (w : BinaryWord) (c : GInt),
      (tileSeqAux prev w).zip (List.scanl (· + ·) c ((w.zip w.tail).map fun ab => hRevOffset ab.1 ab.2)) =
        hAuxG revStr prev w c := by
    intro prev w
    induction w generalizing prev with
    | nil => intro c; rfl
    | cons a rest ih =>
      intro c
      cases rest with
      | nil => rfl
      | cons b rest' =>
        have := ih (some a) (c + hRevOffset a b)
        rw [tileSeqAux_cons, List.tail_cons, List.zip_cons_cons, List.map_cons, List.scanl_cons, List.zip_cons_cons]
        exact congrArg _ this
  exact key none u c

/-! ### The local checks -/

/-- The local conditions of two consecutive tiles of types `t`, `t'` with step `d`: agreement on the overlap, compatibility of
non-overlapping neighbours (the boundary clause of `PTFamily.Respects` in relative coordinates), and adjacency. -/
def PairOK (D : HStr) (t t' : ZTile) (d : GInt) : Prop :=
  (∀ u ∈ tileShape t, ∀ v ∈ tileShape t', u = v + d → relOdo D t u = relOdo D t' v) ∧
  ((¬ ∃ u ∈ tileShape t, ∃ v ∈ tileShape t', u = v + d) →
    ∀ u ∈ tileShape t, ∀ v ∈ tileShape t', (u.1 - (v + d).1).natAbs + (u.2 - (v + d).2).natAbs = 1 →
      relOdo D t u - relOdo D t' v = ptDot (D.alph t) (u - (v + d))) ∧
  ((∃ u ∈ tileShape t, ∃ v ∈ tileShape t', u = v + d) ∨
    ∃ u ∈ tileShape t, ∃ v ∈ tileShape t', (u.1 - (v + d).1).natAbs + (u.2 - (v + d).2).natAbs = 1)

theorem pairOK_fwd (prev : Option Letter) (a b : Letter) :
    PairOK fwdStr (tileFor prev a) (tileFor (some a) b) (fwdStr.step a b) := by
  unfold PairOK
  rcases prev with _ | _ | _ <;> cases a <;> cases b <;> decide

theorem pairOK_rev (prev : Option Letter) (a b : Letter) :
    PairOK revStr (tileFor prev a) (tileFor (some a) b) (revStr.step a b) := by
  unfold PairOK
  rcases prev with _ | _ | _ <;> cases a <;> cases b <;> decide

/-- Two tiles two steps apart are disjoint. -/
def TripleOK (D : HStr) : Prop :=
  ∀ t0 t1 t2 : ZTile, ∀ u ∈ tileShape t0, ∀ v ∈ tileShape t2,
    u ≠ v + (D.step (zTileLetter t0) (zTileLetter t1) + D.step (zTileLetter t1) (zTileLetter t2))

theorem triple_fwd : TripleOK fwdStr := by
  intro t0 t1 t2
  cases t0 <;> cases t1 <;> cases t2 <;> decide

theorem triple_rev : TripleOK revStr := by
  intro t0 t1 t2
  cases t0 <;> cases t1 <;> cases t2 <;> decide

theorem step_bounds_fwd (a b : Letter) : 1 ≤ (fwdStr.step a b).1 ∧ (fwdStr.step a b).1 ≤ 2 := by
  cases a <;> cases b <;> decide

theorem step_bounds_rev (a b : Letter) : 1 ≤ (revStr.step a b).1 ∧ (revStr.step a b).1 ≤ 2 := by
  cases a <;> cases b <;> decide

theorem shape_bounds (t : ZTile) : ∀ u ∈ tileShape t, -1 ≤ u.1 ∧ u.1 ≤ 1 := by
  cases t <;> decide

/-- The slope table: the slope of the explicit odometer of a tile is the base slope plus its affine factor. -/
def TableOK (D : HStr) : Prop :=
  ∀ t t' : ZTile, zTileBaseSlope t' + (((D.alph t').1 : ℚ), ((D.alph t').2 : ℚ)) -
      (zTileBaseSlope t + (((D.alph t).1 : ℚ), ((D.alph t).2 : ℚ))) =
    surgicalSlopeDiff .horizontal D.rev (zTileLetter t) (zTileLetter t')

theorem table_ok_fwd : TableOK fwdStr := by
  intro t t'
  show _ = surgicalSlopeDiff .horizontal false (zTileLetter t) (zTileLetter t')
  rw [table_fwd]
  simp [fwdStr]

theorem table_ok_rev : TableOK revStr := by
  intro t t'
  show _ = surgicalSlopeDiff .horizontal true (zTileLetter t) (zTileLetter t')
  cases t <;> cases t' <;>
    simp only [revStr, surgicalSlopeDiff, zTileLetter, zTileBaseSlope_zero, zTileBaseSlope_one, zTileBaseSlope_oneD] <;>
    refine Prod.ext ?_ ?_ <;> norm_num

/-! ### The chain of consecutive tiles -/

/-- Consecutive elements of a list satisfy `R`. -/
def ConsecOK {α : Type*} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => R a b ∧ ConsecOK R (b :: l)

/-- Two consecutive placed tiles: the step is the one of their letters, and the local conditions hold. -/
def LocalOK (D : HStr) (x y : ZTile × GInt) : Prop :=
  y.2 - x.2 = D.step (zTileLetter x.1) (zTileLetter y.1) ∧
    PairOK D x.1 y.1 (D.step (zTileLetter x.1) (zTileLetter y.1))

theorem hAuxG_chain (D : HStr) (hpair : ∀ prev a b, PairOK D (tileFor prev a) (tileFor (some a) b) (D.step a b)) :
    ∀ (prev : Option Letter) (w : BinaryWord) (c : GInt), ConsecOK (LocalOK D) (hAuxG D prev w c) := by
  intro prev w
  induction w generalizing prev with
  | nil => intro c; trivial
  | cons a rest ih =>
    intro c
    cases rest with
    | nil => trivial
    | cons b rest' =>
      have hc := ih (some a) (c + D.step a b)
      have hh : ∃ tl, hAuxG D (some a) (b :: rest') (c + D.step a b) = (tileFor (some a) b, c + D.step a b) :: tl := by
        cases rest' <;> exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hh
      show ConsecOK (LocalOK D) ((tileFor prev a, c) :: hAuxG D (some a) (b :: rest') (c + D.step a b))
      rw [htl] at hc ⊢
      refine ⟨⟨?_, ?_⟩, hc⟩
      · simp only [zTileLetter_tileFor]
        abel
      · simp only [zTileLetter_tileFor]
        exact hpair prev a b

theorem chain'_getD {α : Type*} {R : α → α → Prop} (d : α) :
    ∀ {L : List α}, ConsecOK R L → ∀ k, k + 1 < L.length → R (L.getD k d) (L.getD (k + 1) d)
  | [], _, k, hk => by simp at hk
  | [_], _, k, hk => by simp at hk
  | a :: b :: l, h, 0, _ => by simpa using h.1
  | a :: b :: l, h, k + 1, hk => by
      have := chain'_getD d h.2 k (by simp only [List.length_cons] at hk ⊢; omega)
      simpa using this

/-! ### The explicit family -/

/-- The explicit family on a list of placed tiles: on each tile, the fixed function of its type at `x - c(T_i)`. -/
def famOf (D : HStr) (L : List (ZTile × GInt)) : PTFamily :=
  { ts := L, a := fun k => D.alph (L.getD k (ZTile.zero, 0)).1,
    b := fun k => D.cst (L.getD k (ZTile.zero, 0)).1 -
      ptDot (D.alph (L.getD k (ZTile.zero, 0)).1) (L.getD k (ZTile.zero, 0)).2 }

theorem famOf_tile (D : HStr) (L : List (ZTile × GInt)) (k : ℕ) : (famOf D L).tile k = L.getD k (ZTile.zero, 0) := rfl

theorem famOf_odo (D : HStr) (L : List (ZTile × GInt)) (k : ℕ) (x : GInt) :
    (famOf D L).odo k x = relOdo D (L.getD k (ZTile.zero, 0)).1 (x - (L.getD k (ZTile.zero, 0)).2) := by
  unfold PTFamily.odo
  rw [famOf_tile]
  simp only [famOf, relOdo, ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem mem_dom_iff (F : PTFamily) (k : ℕ) (x : GInt) :
    x ∈ F.dom k ↔ x - (F.tile k).2 ∈ tileShape (F.tile k).1 := by
  unfold PTFamily.dom
  rw [chain_mem_map_add_iff]

theorem famOf_n (D : HStr) (L : List (ZTile × GInt)) : (famOf D L).n = L.length := rfl

/-- The positions advance by at least one in the first coordinate at each step; two steps are the sum of two letter steps. -/
theorem pos_advance (D : HStr) (hb : ∀ a b, 1 ≤ (D.step a b).1) (L : List (ZTile × GInt))
    (hL : ConsecOK (LocalOK D) L) (i : ℕ) :
    ∀ m, i + m < L.length → (m : ℤ) ≤ ((L.getD (i + m) (ZTile.zero, 0)).2 - (L.getD i (ZTile.zero, 0)).2).1 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := (chain'_getD (ZTile.zero, (0 : GInt)) hL (i + m) (by omega)).1
    have h3 := hb (zTileLetter (L.getD (i + m) (ZTile.zero, 0)).1) (zTileLetter (L.getD (i + m + 1) (ZTile.zero, 0)).1)
    rw [← h2] at h3
    rw [show i + (m + 1) = i + m + 1 by omega]
    simp only [Prod.fst_sub] at h1 h3 ⊢
    push_cast
    linarith

/-- Non-consecutive tiles of the string are disjoint. -/
theorem far_disjoint (D : HStr) (hb : ∀ a b, 1 ≤ (D.step a b).1) (ht : TripleOK D) (L : List (ZTile × GInt))
    (hL : ConsecOK (LocalOK D) L) (k j : ℕ) (hkj : k + 2 ≤ j) (hj : j < L.length) (x : GInt)
    (hxk : x ∈ (famOf D L).dom k) (hxj : x ∈ (famOf D L).dom j) : False := by
  rw [mem_dom_iff, famOf_tile] at hxk hxj
  have bk := shape_bounds _ _ hxk
  have bj := shape_bounds _ _ hxj
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
  have hadv := pos_advance D hb L hL k m hj
  simp only [Prod.fst_sub] at bk bj hadv
  by_cases hm : m = 2
  · subst hm
    have s1 := (chain'_getD (ZTile.zero, (0 : GInt)) hL k (by omega)).1
    have s2 := (chain'_getD (ZTile.zero, (0 : GInt)) hL (k + 1) (by omega)).1
    refine ht (L.getD k (ZTile.zero, 0)).1 (L.getD (k + 1) (ZTile.zero, 0)).1 (L.getD (k + 2) (ZTile.zero, 0)).1 _ hxk _ hxj ?_
    rw [← s1, ← s2]
    abel
  · have : (3 : ℤ) ≤ m := by omega
    omega

/-- The explicit family is well defined: on the intersection of two of its tiles the two odometers agree. -/
theorem famOf_wd (D : HStr) (hb : ∀ a b, 1 ≤ (D.step a b).1) (ht : TripleOK D) (L : List (ZTile × GInt))
    (hL : ConsecOK (LocalOK D) L) :
    ∀ k < (famOf D L).n, ∀ j < (famOf D L).n, ∀ x ∈ (famOf D L).dom k, x ∈ (famOf D L).dom j →
      (famOf D L).odo k x = (famOf D L).odo j x := by
  have adj : ∀ k, k + 1 < L.length → ∀ x ∈ (famOf D L).dom k, x ∈ (famOf D L).dom (k + 1) →
      (famOf D L).odo k x = (famOf D L).odo (k + 1) x := by
    intro k hk x hx hy
    obtain ⟨hs, hov, -, -⟩ := chain'_getD (ZTile.zero, (0 : GInt)) hL k hk
    rw [mem_dom_iff, famOf_tile] at hx hy
    rw [famOf_odo, famOf_odo]
    refine hov _ hx _ hy ?_
    rw [← hs]
    abel
  intro k hk j hj x hxk hxj
  rw [famOf_n] at hk hj
  rcases lt_trichotomy k j with h | rfl | h
  · by_cases h1 : j = k + 1
    · subst h1; exact adj k hj x hxk hxj
    · exact (far_disjoint D hb ht L hL k j (by omega) hj x hxk hxj).elim
  · rfl
  · by_cases h1 : k = j + 1
    · subst h1; exact (adj j hk x hxj hxk).symm
    · exact (far_disjoint D hb ht L hL j k (by omega) hk x hxj hxk).elim

theorem unitApart_shift (u v p : GInt) : unitApart (u + p) (v + p) ↔ unitApart u v := by
  unfold unitApart
  simp only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

/-- The explicit family respects the string. -/
theorem famOf_respects (D : HStr) (htab : TableOK D) (L : List (ZTile × GInt)) (hL : ConsecOK (LocalOK D) L) :
    (famOf D L).Respects .horizontal D.rev := by
  intro k hk
  rw [famOf_n] at hk
  obtain ⟨hs, -, hbd, -⟩ := chain'_getD (ZTile.zero, (0 : GInt)) hL k hk
  refine ⟨?_, ?_⟩
  · have hsl : ∀ i, slopeOf ((famOf D L).odo i) ((famOf D L).dom i) =
        zTileBaseSlope ((famOf D L).tile i).1 +
          ((((famOf D L).a i).1 : ℚ), (((famOf D L).a i).2 : ℚ)) := by
      intro i
      have hodo : (famOf D L).odo i = fun y => zTileOdo ((famOf D L).tile i).1 (y - ((famOf D L).tile i).2) +
          ((famOf D L).a i).1 * y.1 + ((famOf D L).a i).2 * y.2 + (famOf D L).b i := rfl
      rw [hodo]
      exact slopeOf_translate_affine _ _ _ _ _ (unitSquares_tileShape_ne _)
    rw [hsl, hsl]
    exact htab _ _
  · intro hno x hx y hy hu
    constructor
    · intro _
      rw [mem_dom_iff, famOf_tile] at hx hy
      have hno' : ¬ ∃ u ∈ tileShape (L.getD k (ZTile.zero, 0)).1, ∃ v ∈ tileShape (L.getD (k + 1) (ZTile.zero, 0)).1,
          u = v + D.step (zTileLetter (L.getD k (ZTile.zero, 0)).1) (zTileLetter (L.getD (k + 1) (ZTile.zero, 0)).1) := by
        rintro ⟨u, hu', v, hv', huv⟩
        apply hno
        refine ⟨u + (L.getD k (ZTile.zero, 0)).2, ?_, ?_⟩
        · rw [mem_dom_iff, famOf_tile]; simpa using hu'
        · rw [mem_dom_iff, famOf_tile, huv, ← hs]
          simpa [add_assoc, add_sub_cancel] using hv'
      have hu2 : ((x - (L.getD k (ZTile.zero, 0)).2).1 -
            ((y - (L.getD (k + 1) (ZTile.zero, 0)).2) + D.step (zTileLetter (L.getD k (ZTile.zero, 0)).1)
              (zTileLetter (L.getD (k + 1) (ZTile.zero, 0)).1)).1).natAbs +
          ((x - (L.getD k (ZTile.zero, 0)).2).2 -
            ((y - (L.getD (k + 1) (ZTile.zero, 0)).2) + D.step (zTileLetter (L.getD k (ZTile.zero, 0)).1)
              (zTileLetter (L.getD (k + 1) (ZTile.zero, 0)).1)).2).natAbs = 1 := by
        rw [← hs]
        unfold unitApart at hu
        simpa using hu
      have key := hbd hno' _ hx _ hy hu2
      simp only [famOf_odo] at *
      rw [← hs] at key
      have e : x - (L.getD k (ZTile.zero, 0)).2 -
          (y - (L.getD (k + 1) (ZTile.zero, 0)).2 + ((L.getD (k + 1) (ZTile.zero, 0)).2 - (L.getD k (ZTile.zero, 0)).2)) =
          x - y := by abel
      rw [e] at key
      simp only [famOf, ptDot, Prod.fst_sub, Prod.snd_sub] at key ⊢
      linarith
    · intro h
      exact absurd h (by simp)

/-- Adjacency of consecutive tiles: they overlap or have a pair of unit-apart sites. -/
theorem famOf_adj (D : HStr) (L : List (ZTile × GInt)) (hL : ConsecOK (LocalOK D) L) :
    ∀ k, k + 1 < (famOf D L).n → (∃ x, x ∈ (famOf D L).dom k ∧ x ∈ (famOf D L).dom (k + 1)) ∨
      ∃ x, x ∈ (famOf D L).dom k ∧ ∃ y, y ∈ (famOf D L).dom (k + 1) ∧ unitApart x y := by
  intro k hk
  rw [famOf_n] at hk
  obtain ⟨hs, -, -, hadj⟩ := chain'_getD (ZTile.zero, (0 : GInt)) hL k hk
  rcases hadj with ⟨u, hu, v, hv, huv⟩ | ⟨u, hu, v, hv, huv⟩
  · left
    refine ⟨u + (L.getD k (ZTile.zero, 0)).2, ?_, ?_⟩
    · rw [mem_dom_iff, famOf_tile]; simpa using hu
    · rw [mem_dom_iff, famOf_tile, huv, ← hs]
      simpa [add_assoc, add_sub_cancel] using hv
  · right
    refine ⟨u + (L.getD k (ZTile.zero, 0)).2, ?_, v + (L.getD (k + 1) (ZTile.zero, 0)).2, ?_, ?_⟩
    · rw [mem_dom_iff, famOf_tile]; simpa using hu
    · rw [mem_dom_iff, famOf_tile]; simpa using hv
    · rw [← hs] at huv
      unfold unitApart
      have e1 : (u + (L.getD k (ZTile.zero, 0)).2).1 - (v + (L.getD (k + 1) (ZTile.zero, 0)).2).1 =
          u.1 - (v + ((L.getD (k + 1) (ZTile.zero, 0)).2 - (L.getD k (ZTile.zero, 0)).2)).1 := by
        simp only [Prod.fst_add, Prod.fst_sub]; ring
      have e2 : (u + (L.getD k (ZTile.zero, 0)).2).2 - (v + (L.getD (k + 1) (ZTile.zero, 0)).2).2 =
          u.2 - (v + ((L.getD (k + 1) (ZTile.zero, 0)).2 - (L.getD k (ZTile.zero, 0)).2)).2 := by
        simp only [Prod.snd_add, Prod.snd_sub]; ring
      rw [e1, e2]
      exact huv

/-! ### The formula -/

/-- Step 1 for a string with the local checks: an odometer respecting the string is, on every tile, the fixed function of the tile
type plus one affine function and one constant. -/
theorem string_formula (D : HStr) (htab : TableOK D) (hb : ∀ a b, 1 ≤ (D.step a b).1) (ht : TripleOK D)
    (L : List (ZTile × GInt)) (hL : ConsecOK (LocalOK D) L) (S : GInt → ℤ) (hR : RespectsTiles .horizontal D.rev L S) :
    ∃ (α : GInt) (β : ℤ), ∀ k < L.length, ∀ x ∈ (famOf D L).dom k,
      S x = relOdo D (L.getD k (ZTile.zero, 0)).1 (x - (L.getD k (ZTile.zero, 0)).2) + ptDot α x + β := by
  obtain ⟨G, hG, hGS, hGR⟩ := hR
  have hts : G.ts = (famOf D L).ts := hG
  obtain ⟨a, c, hac⟩ := PTFamily.exists_affine_of_respects_gen .horizontal D.rev (famOf D L) G hts
    (famOf_respects D htab L hL) hGR (famOf_wd D hb ht L hL)
    (by
      intro k hk j hj x hxk hxj
      rw [← hGS k hk x hxk, ← hGS j hj x hxj])
    (famOf_adj D L hL)
  refine ⟨a, c, fun k hk x hx => ?_⟩
  have hkG : k < G.n := by rw [PTFamily.n_eq_of_ts _ _ hts]; exact hk
  have hxG : x ∈ G.dom k := by rw [PTFamily.dom_eq_of_ts (famOf D L) G hts]; exact hx
  rw [hGS k hkG x hxG, hac k hk x, famOf_odo]
  simp only [ptDot]
  ring

/-- Step 1 for the forward horizontal string `w_h` at `c`: on every tile, the zero-one odometer of its type plus one affine
function and one constant. -/
theorem horizontal_formula (wh : BinaryWord) (c : GInt) (S : GInt → ℤ)
    (hR : RespectsTiles .horizontal false (hStringAt wh c) S) :
    ∃ (α : GInt) (β : ℤ), ∀ k < (hStringAt wh c).length, ∀ x ∈ (famOf fwdStr (hStringAt wh c)).dom k,
      S x = zTileOdo ((hStringAt wh c).getD k (ZTile.zero, 0)).1 (x - ((hStringAt wh c).getD k (ZTile.zero, 0)).2) +
        ptDot α x + β := by
  have hL : ConsecOK (LocalOK fwdStr) (hStringAt wh c) := by
    rw [hStringAt_eq]; exact hAuxG_chain fwdStr pairOK_fwd none wh c
  obtain ⟨α, β, h⟩ := string_formula fwdStr table_ok_fwd (fun a b => (step_bounds_fwd a b).1) triple_fwd _ hL S hR
  refine ⟨α, β, fun k hk x hx => ?_⟩
  rw [h k hk x hx]
  simp [relOdo, fwdStr, ptDot]

/-- Step 1 for the reversed horizontal string `u` at `c`: on every tile, the odometer `ô` of its type plus one affine function and
one constant. -/
theorem reversed_horizontal_formula (u : BinaryWord) (c : GInt) (S : GInt → ℤ)
    (hR : RespectsTiles .horizontal true (hRevStringAt u c) S) :
    ∃ (α : GInt) (β : ℤ), ∀ k < (hRevStringAt u c).length, ∀ x ∈ (famOf revStr (hRevStringAt u c)).dom k,
      S x = relOdo revStr ((hRevStringAt u c).getD k (ZTile.zero, 0)).1 (x - ((hRevStringAt u c).getD k (ZTile.zero, 0)).2) +
        ptDot α x + β := by
  have hL : ConsecOK (LocalOK revStr) (hRevStringAt u c) := by
    rw [hRevStringAt_eq]; exact hAuxG_chain revStr pairOK_rev none u c
  exact string_formula revStr table_ok_rev (fun a b => (step_bounds_rev a b).1) triple_rev _ hL S hR

/-! ### The bottom corner values of `eq:std_corner_values` -/

theorem hAuxG_head (D : HStr) (prev : Option Letter) (a : Letter) (rest : BinaryWord) (c : GInt) :
    (hAuxG D prev (a :: rest) c).getD 0 (ZTile.zero, 0) = (tileFor prev a, c) := by
  cases rest <;> rfl

theorem hAuxG_last_fst (D : HStr) : ∀ (prev : Option Letter) (w : BinaryWord) (c : GInt), w.getLast? = some Letter.p →
    (hAuxG D prev w c).getLast?.map (·.1) = some ZTile.zero := by
  intro prev w
  induction w generalizing prev with
  | nil => intro c h; simp at h
  | cons a rest ih =>
    intro c h
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      rfl
    | cons b rest' =>
      have h' : (b :: rest').getLast? = some Letter.p := by simpa [List.getLast?_cons_cons] using h
      have := ih (some a) (c + D.step a b) h'
      have hh : ∃ tl, hAuxG D (some a) (b :: rest') (c + D.step a b) = (tileFor (some a) b, c + D.step a b) :: tl := by
        cases rest' <;> exact ⟨_, rfl⟩
      obtain ⟨tl, htl⟩ := hh
      show (((tileFor prev a, c) :: hAuxG D (some a) (b :: rest') (c + D.step a b)).getLast?.map (·.1)) = _
      rw [htl] at this ⊢
      simpa [List.getLast?_cons_cons] using this

/-- The bottom corner values of `eq:std_corner_values`: if `S` respects the forward horizontal string of a word from `q` to `p`
whose last tile sits at `X - 1 - i`, then for the normalisation `(α, β)` of the formula (`S - α^T x - β = o_{1/1}` on the first
tile at the origin), `S - α^T x - β` vanishes at `0`, `1`, `X - i` and `X`. -/
theorem bottom_corner_values (wh : BinaryWord) (S : GInt → ℤ) (X : GInt) (hhead : wh.head? = some Letter.q)
    (hlast : wh.getLast? = some Letter.p) (hX : lastPosOf (hStringAt wh 0) = X - (1, 1))
    (hR : RespectsTiles .horizontal false (hStringAt wh 0) S) :
    ∃ (α : GInt) (β : ℤ), (∀ x ∈ tileShape ZTile.one, S x - ptDot α x - β = zTileOdo ZTile.one x) ∧
      S 0 - ptDot α 0 - β = 0 ∧ S (1, 0) - ptDot α (1, 0) - β = 0 ∧
      S (X - (0, 1)) - ptDot α (X - (0, 1)) - β = 0 ∧ S X - ptDot α X - β = 0 := by
  obtain ⟨α, β, h⟩ := horizontal_formula wh 0 S hR
  obtain ⟨rest, rfl⟩ : ∃ rest, wh = Letter.q :: rest := by
    cases wh with
    | nil => simp at hhead
    | cons a rest => simp only [List.head?_cons, Option.some.injEq] at hhead; exact ⟨rest, by rw [hhead]⟩
  set L := hStringAt (Letter.q :: rest) 0 with hLdef
  have hlen : 0 < L.length := by rw [hLdef, hStringAt_eq]; cases rest <;> simp [hAuxG]
  have h0 : L.getD 0 (ZTile.zero, 0) = (ZTile.one, 0) := by
    rw [hLdef, hStringAt_eq, hAuxG_head]; rfl
  have hlastT : L.getLast?.map (·.1) = some ZTile.zero := by
    rw [hLdef, hStringAt_eq]; exact hAuxG_last_fst fwdStr none _ 0 hlast
  have hlastP : L.getLast?.map (·.2) = some (X - (1, 1)) := by
    have hne : L.getLast? ≠ none := by
      intro hn; rw [hn] at hlastT; simp at hlastT
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hne
    unfold lastPosOf at hX
    rw [he] at hX
    rw [he]
    simpa using hX
  have hlastE : L.getD (L.length - 1) (ZTile.zero, 0) = (ZTile.zero, X - (1, 1)) := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
    obtain ⟨e, he⟩ : ∃ e, L.getLast? = some e := by
      cases hL : L.getLast? with
      | none => rw [hL] at hlastT; simp at hlastT
      | some e => exact ⟨e, rfl⟩
    rw [he] at hlastT hlastP ⊢
    simp only [Option.map_some, Option.some.injEq] at hlastT hlastP
    simp only [Option.getD_some]
    exact Prod.ext hlastT hlastP
  have v0 : ∀ x ∈ tileShape ZTile.one, S x = zTileOdo ZTile.one x + ptDot α x + β := by
    intro x hx
    have := h 0 hlen x (by rw [mem_dom_iff, famOf_tile, h0]; simpa using hx)
    rw [this, h0]
    simp
  have vL : ∀ y ∈ tileShape ZTile.zero, S (y + (X - (1, 1))) = zTileOdo ZTile.zero y + ptDot α (y + (X - (1, 1))) + β := by
    intro y hy
    have := h (L.length - 1) (by omega) (y + (X - (1, 1))) (by rw [mem_dom_iff, famOf_tile, hlastE]; simpa using hy)
    rw [this, hlastE]
    simp
  refine ⟨α, β, fun x hx => by rw [v0 x hx]; ring, ?_, ?_, ?_, ?_⟩
  · have z : zTileOdo ZTile.one 0 = 0 := by decide
    rw [v0 0 (by decide), z]; ring
  · have z : zTileOdo ZTile.one (1, 0) = 0 := by decide
    rw [v0 (1, 0) (by decide), z]; ring
  · have e : X - (0, 1) = ((1 : ℤ), (0 : ℤ)) + (X - (1, 1)) := by ext <;> simp
    have z : zTileOdo ZTile.zero (1, 0) = 0 := by decide
    rw [e, vL (1, 0) (by decide), z]; ring
  · have e : X = ((1 : ℤ), (1 : ℤ)) + (X - (1, 1)) := by ext <;> simp
    have z : zTileOdo ZTile.zero (1, 1) = 0 := by decide
    rw [e, vL (1, 1) (by decide), z]; ring

end FLatticePaper.Tiles.HorizontalStepOne
