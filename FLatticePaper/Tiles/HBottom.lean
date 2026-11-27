import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.SiteStrings
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.SurgicalAffineChain

/-! The bottom walk of a horizontal string (H2, hB), first step: the displacement of a `gPair` segment.

A zero-one tile has an anchor: `zero` and `one` are anchored at their origin, the enlarged `oneD` at its origin plus `(1,-1)`.
Entering a tile moves the origin by `incr` (horizontal origin step: `(2,0)` for a `p`, `(1,1)` for a `q`, `dxdy`). For every pair
of consecutive tiles that the tile sequence produces, the walk segment `gPair a b` has displacement `incr b + off b - off a`. -/

namespace FLatticePaper.Tiles.HBottom

open FLatticePaper.Tiles FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings

/-- The anchor offset of a zero-one tile. -/
def anchorOff : ZTile → GInt
  | .zero => (0, 0)
  | .one => (0, 0)
  | .oneD => (1, -1)

/-- The origin increment of entering a tile. -/
def incr : ZTile → GInt
  | .zero => (2, 0)
  | .one => (1, 1)
  | .oneD => (1, 1)

/-- The pairs of consecutive tiles that `tileSeq` never produces are excluded. -/
def ValidPair (a b : ZTile) : Prop :=
  ¬ ((a = .zero ∧ b = .oneD) ∨ (a = .one ∧ b = .one) ∨ (a = .oneD ∧ b = .one))

/-- The displacement of the `gPair` segment of a valid pair is the origin step of its second tile, plus the anchor change. -/
theorem sum_gPair (a b : ZTile) (h : ValidPair a b) :
    F2Word.sum (gPair a b) = incr b + anchorOff b - anchorOff a := by
  cases a <;> cases b <;> simp_all [ValidPair, gPair, incr, anchorOff, F2Word.sum, Unit4.vec]

/-- The base sites of a zero-one tile, relative to its origin (`baseSites` of its letter; `oneD` is the enlarged `q`). -/
def baseOf : ZTile → List (ℤ × ℤ)
  | .zero => FLatticePaper.Tiles.SiteStrings.baseSites Letter.p false
  | .one => FLatticePaper.Tiles.SiteStrings.baseSites Letter.q false
  | .oneD => FLatticePaper.Tiles.SiteStrings.baseSites Letter.q true

/-- The points of the walk of a valid pair segment lie in the base sites of one of its two tiles (offsets from the origin of
the first tile, and from the origin of the second tile, which is `incr b` further). -/
theorem walk_gPair_mem (a b : ZTile) (h : ValidPair a b) (x : GInt)
    (hx : x ∈ F2Word.walk (anchorOff a) (gPair a b)) :
    x ∈ baseOf a ∨ x - incr b ∈ baseOf b := by
  have key : ∀ a b : ZTile, ValidPair a b →
      (F2Word.walk (anchorOff a) (gPair a b)).all
        (fun x => decide (x ∈ baseOf a) || decide (x - incr b ∈ baseOf b)) = true := by
    intro a b hab
    cases a <;> cases b <;> first | exact (hab (by decide)).elim | decide
  have hk := List.all_eq_true.1 (key a b h) x hx
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using hk

/-! ### The walk of a horizontal string, tile by tile

The walk of `gH h` is the chain of the `gPair` segments of the consecutive tiles of `h`, then a final `1`. Each segment starts at the
anchor of its tile, and its points lie in the base sites of its tile or of the next one (`walk_gPair_mem`). The origin of the next
tile is the origin of this one plus `dxdy`, which is the `incr` of the next tile, so the points lie in the string sites. -/

/-- The tile of a letter read after the previous letter (the tile of `tileSeqAux`). -/
def zTileOf : Option Letter → Letter → ZTile
  | _, .p => .zero
  | some .q, .q => .oneD
  | _, .q => .one

/-- The enlargement flag of a letter read after the previous letter: a `q` after a `q`. -/
def flagOf : Option Letter → Letter → Bool
  | some .q, .q => true
  | _, _ => false

/-- The `gPair` segments of the consecutive tiles of a tile list (the first factor of `gH`). -/
def chainOf (ts : List ZTile) : F2Word := (ts.zip ts.tail).flatMap fun ab => gPair ab.1 ab.2

/-- The sites of one entry of a string: the base sites of its letter, from its origin. -/
def entSites (e : GInt × Letter × Bool) : List GInt :=
  (baseSites e.2.1 e.2.2).map fun b => (e.1.1 + b.1, e.1.2 + b.2)

theorem gH_unfold (w : BinaryWord) : gH w = chainOf (tileSeq w) ++ [Unit4.one] := rfl

theorem tileSeqAux_cons (pr : Option Letter) (l : Letter) (ls : BinaryWord) :
    tileSeqAux pr (l :: ls) = zTileOf pr l :: tileSeqAux (some l) ls := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases l <;> rfl

theorem chainOf_cons_cons (t t' : ZTile) (rest : List ZTile) :
    chainOf (t :: t' :: rest) = gPair t t' ++ chainOf (t' :: rest) := by
  simp [chainOf]

theorem baseOf_zTileOf (pr : Option Letter) (l : Letter) :
    baseOf (zTileOf pr l) = baseSites l (flagOf pr l) := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases l <;> rfl

theorem anchor_mem (pr : Option Letter) (l : Letter) :
    anchorOff (zTileOf pr l) ∈ baseSites l (flagOf pr l) := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases l <;> decide

theorem anchor_step_mem (pr : Option Letter) :
    anchorOff (zTileOf pr .p) + Unit4.one.vec ∈ baseSites .p (flagOf pr .p) := by
  rcases pr with _ | ⟨_ | _⟩ <;> decide

theorem dxdy_eq_incr (l l' : Letter) :
    dxdy false false l l' = incr (zTileOf (some l) l') := by
  cases l <;> cases l' <;> rfl

theorem validPair_zTileOf (pr : Option Letter) (l l' : Letter) :
    ValidPair (zTileOf pr l) (zTileOf (some l) l') := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases l <;> cases l' <;> simp only [ValidPair, zTileOf] <;> decide

theorem walk_shift (o a : GInt) (w : F2Word) :
    F2Word.walk (o + a) w = (F2Word.walk a w).map (fun z => o + z) := by
  simp only [WalkDecomp.walk_translate (o + a) w, WalkDecomp.walk_translate a w, List.map_map, Function.comp_def, add_assoc]

theorem origins_cons_eq (o : GInt) (pr l : Letter) (ls : List Letter) :
    origins false false (some pr) o (l :: ls)
      = (o + dxdy false false pr l, l, flagOf (some pr) l)
          :: origins false false (some l) (o + dxdy false false pr l) ls := by
  cases pr <;> cases l <;> rfl

theorem mem_entSites (o b : GInt) (l : Letter) (f : Bool) (hb : b ∈ baseSites l f) :
    o + b ∈ entSites (o, l, f) :=
  List.mem_map.2 ⟨b, hb, rfl⟩

/-- The walk of a chain of tiles, from the anchor of its first tile and followed by the final `1`, lies in the entries of the
string. The final `1` ends in the base sites of a last `p`, which is the hypothesis `hp`. -/
theorem walk_mem_entries (ls : List Letter) : ∀ (pr : Option Letter) (o : GInt) (l : Letter),
    (l :: ls).getLast? = some .p →
    ∀ x ∈ F2Word.walk (o + anchorOff (zTileOf pr l))
        (chainOf (zTileOf pr l :: tileSeqAux (some l) ls) ++ [Unit4.one]),
      x ∈ ((o, l, flagOf pr l) :: origins false false (some l) o ls).flatMap entSites := by
  induction ls with
  | nil =>
    intro pr o l hp x hx
    have hl : l = .p := by simpa using hp
    subst hl
    have hc : chainOf (zTileOf pr .p :: tileSeqAux (some .p) []) = [] := by
      simp [chainOf, tileSeqAux]
    rw [hc, List.nil_append, WalkDecomp.walk_cons, WalkDecomp.walk_nil] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    simp only [origins, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases hx with rfl | rfl
    · exact mem_entSites o _ .p _ (anchor_mem pr .p)
    · rw [add_assoc]
      exact mem_entSites o _ .p _ (anchor_step_mem pr)
  | cons l' ls ih =>
    intro pr o l hp x hx
    have hp' : (l' :: ls).getLast? = some .p := by simpa using hp
    rw [tileSeqAux_cons (some l) l' ls, chainOf_cons_cons, List.append_assoc] at hx
    rw [origins_cons_eq o l l' ls]
    rw [WalkDecomp.walk_append, List.mem_append] at hx
    have hv := validPair_zTileOf pr l l'
    rcases hx with h1 | h2
    · rw [walk_shift, List.mem_map] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      subst hyx
      show o + y ∈ _
      rcases walk_gPair_mem _ _ hv y hy with hb | hb
      · rw [baseOf_zTileOf] at hb
        exact List.mem_flatMap.2 ⟨(o, l, flagOf pr l), by simp, mem_entSites o y l (flagOf pr l) hb⟩
      · rw [baseOf_zTileOf] at hb
        refine List.mem_flatMap.2 ⟨(o + dxdy false false l l', l', flagOf (some l) l'), by simp, ?_⟩
        have e : o + y = (o + dxdy false false l l') + (y - incr (zTileOf (some l) l')) := by
          rw [dxdy_eq_incr]; abel
        rw [e]
        exact mem_entSites _ _ l' _ hb
    · have hs := sum_gPair _ _ hv
      have hc : (o + anchorOff (zTileOf pr l)) + F2Word.sum (gPair (zTileOf pr l) (zTileOf (some l) l'))
          = (o + dxdy false false l l') + anchorOff (zTileOf (some l) l') := by
        rw [hs, dxdy_eq_incr]; abel
      rw [hc] at h2
      have h3 := ih (some l) (o + dxdy false false l l') l' hp' x (List.mem_of_mem_tail h2)
      rw [List.flatMap_cons, List.mem_append]
      exact Or.inr h3

/-- The walk of `gH h` from `0` lies in the string sites of a horizontal word `h` ending in `p`. -/
theorem gH_walk_mem (h : List Letter) (hp : h.getLast? = some .p) :
    ∀ x ∈ F2Word.walk 0 (gH h), x ∈ stringSites false false h := by
  cases h with
  | nil => simp at hp
  | cons l0 ls0 =>
    intro x hx
    have hz : (0 : GInt) + anchorOff (zTileOf none l0) = 0 := by cases l0 <;> rfl
    have hx' : x ∈ F2Word.walk (0 + anchorOff (zTileOf none l0))
        (chainOf (zTileOf none l0 :: tileSeqAux (some l0) ls0) ++ [Unit4.one]) := by
      rw [hz]
      rw [gH_unfold, tileSeq, tileSeqAux_cons] at hx
      exact hx
    have key := walk_mem_entries ls0 none 0 l0 hp x hx'
    have hs : stringSites false false (l0 :: ls0)
        = (((0 : GInt), l0, flagOf none l0) :: origins false false (some l0) 0 ls0).flatMap entSites := rfl
    rw [hs]
    exact key

/-- **hB for the odd child.** The bottom walk of the odd child lies in the horizontal string sites of its word `hWordOf w false`. -/
theorem hB_odd (w : Word) :
    ∀ s ∈ F2Word.walk 0 (FLatticePaper.Tiles.StandardBoundary.oddBottom w),
      s ∈ stringSites false false (hWordOf w false) := by
  intro s hs
  have e : FLatticePaper.Tiles.StandardBoundary.oddBottom w = gH (hWordOf w false) :=
    FLatticePaper.Tiles.RegisterLink.oddBottom_eq_gH w
  rw [e] at hs
  exact gH_walk_mem _ (FLatticePaper.Tiles.hWordOf_head_last w false).2 s hs

/-- **hB for the even child.** The bottom walk of the even child lies in the horizontal string sites of its word `hWordOf w true`. -/
theorem hB_even (w : Word) :
    ∀ s ∈ F2Word.walk 0 (FLatticePaper.Tiles.StandardBoundary.evenBottom w),
      s ∈ stringSites false false (hWordOf w true) := by
  intro s hs
  have e : FLatticePaper.Tiles.StandardBoundary.evenBottom w = gH (hWordOf w true) :=
    FLatticePaper.Tiles.RegisterLink.evenBottom_eq_gH w
  rw [e] at hs
  exact gH_walk_mem _ (FLatticePaper.Tiles.hWordOf_head_last w true).2 s hs

end FLatticePaper.Tiles.HBottom
