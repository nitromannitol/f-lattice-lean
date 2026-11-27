import FLatticePaper.Tiles.HBottom
import FLatticePaper.Tiles.VerticalRight
import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.CornerPositions
import FLatticePaper.Tiles.StandardBoundary

/-! S3' of the vertical overlap form of H2: the right walk of a standard tile is covered by its vertical string.

The right walk is the rotated horizontal walk `map mulI (gH h)` (`VerticalRight`). The vertical string `vStringAt (flipW h)` has
tiles of the flipped letters, with origin steps `rotI` of the horizontal steps (`vOffset (flip x) = rotI (hOffset x)`). So the vertical
tile list of a tile sequence is `vtl`, and the rotated walk is covered by it, segment by segment: the start of each pair lies in the
tile of the pair or of the one before, and its middle point lies in the tile of the pair or of the one after (finite checks,
`win_start` and `win_mid`). -/

namespace FLatticePaper.Tiles.VerticalCover

open FLatticePaper.Tiles FLatticePaper.Tiles.HBottom FLatticePaper.Tiles.ReflectedCover FLatticePaper.Farey
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary
open FLatticePaper.Tiles.VerticalRight

/-- The vertical tile of a horizontal tile type: the letters are exchanged, so `zero` (letter `p`) gives the `one` shape. -/
def vtileOf : ZTile → ZTile
  | .zero => .one
  | .one => .zero
  | .oneD => .zero

/-- The vertical tile list of a tile sequence from an origin: the origin step into a tile is the rotation of its horizontal step. -/
def vtl : List ZTile → GInt → List (ZTile × GInt)
  | [], _ => []
  | [t], o => [(vtileOf t, o)]
  | t :: t' :: ts, o => (vtileOf t, o) :: vtl (t' :: ts) (o + rotI (incr t'))

/-- The rotated walk generator of a tile sequence: the `i`-multiples of the `gPair` segments. -/
def chainMV (ts : List ZTile) : F2Word :=
  (ts.zip ts.tail).flatMap fun ab => (gPair ab.1 ab.2).map Unit4.mulI

theorem vStringAt_cons (a b : Letter) (w : BinaryWord) (c : GInt) :
    vStringAt (a :: b :: w) c = (letterZTile a, c) :: vStringAt (b :: w) (c + vOffset b) := by
  unfold vStringAt
  simp [List.scanl_cons]

theorem vStringAt_single (a : Letter) (c : GInt) : vStringAt [a] c = [(letterZTile a, c)] := by
  simp [vStringAt]

theorem vOffset_flip (x : Letter) : vOffset (flipLetter x) = rotI (hOffset x) := by
  cases x <;> rfl

theorem vtileOf_zTileOf (pr : Option Letter) (x : Letter) :
    vtileOf (zTileOf pr x) = letterZTile (flipLetter x) := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases x <;> rfl

theorem incr_zTileOf (pr : Option Letter) (x : Letter) : incr (zTileOf pr x) = hOffset x := by
  rcases pr with _ | ⟨_ | _⟩ <;> cases x <;> rfl

/-- The vertical string of the flipped word is the vertical tile list of its tile sequence. -/
theorem vStringAt_flip (w : BinaryWord) : ∀ (pr : Option Letter) (c : GInt),
    vStringAt (flipW w) c = vtl (tileSeqAux pr w) c := by
  induction w with
  | nil => intro pr c; simp [flipW, vStringAt, tileSeqAux, vtl]
  | cons x w ih =>
    intro pr c
    cases w with
    | nil =>
      simp only [flipW, List.map_cons, List.map_nil]
      rw [vStringAt_single, tileSeqAux_cons]
      simp [vtl, vtileOf_zTileOf, tileSeqAux]
    | cons y w' =>
      have e1 : flipW (x :: y :: w') = flipLetter x :: flipLetter y :: flipW w' := by simp [flipW]
      have e2 : flipW (y :: w') = flipLetter y :: flipW w' := by simp [flipW]
      rw [e1, vStringAt_cons, ← e2, ih (some x) (c + vOffset (flipLetter y)), tileSeqAux_cons pr x (y :: w'),
        tileSeqAux_cons (some x) y w']
      rw [vtl, vtileOf_zTileOf, incr_zTileOf, vOffset_flip]

/-! ### Finite window checks and the covering helpers -/

/-- Adjacent tiles of a chain are valid pairs. -/
def ValidChain : List ZTile → Prop
  | [] => True
  | [_] => True
  | t :: t' :: ts => ValidPair t t' ∧ ValidChain (t' :: ts)

/-- The first unit of the segment of a pair. -/
def firstUnit (t t' : ZTile) : Unit4 := (gPair t t').headD .one

theorem chainMV_cons2 (t t' : ZTile) (ts : List ZTile) :
    chainMV (t :: t' :: ts) = (gPair t t').map Unit4.mulI ++ chainMV (t' :: ts) := by
  simp [chainMV, List.zip_cons_cons, List.flatMap_cons]

theorem gPair_two (t t' : ZTile) (hv : ValidPair t t') : ∃ g0 g1, gPair t t' = [g0, g1] := by
  simp only [ValidPair] at hv
  cases t <;> cases t' <;> first | exact ⟨_, _, rfl⟩ | exact (hv (by decide)).elim

theorem win_start (p t : ZTile) (hv : ValidPair p t) :
    rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) ∈ tileShape (vtileOf t) ∨
    rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + rotI (incr t) ∈ tileShape (vtileOf p) := by
  simp only [ValidPair] at hv
  cases p <;> cases t <;> first | exact (hv (by decide)).elim | decide

theorem win_mid (t t' : ZTile) (hv : ValidPair t t') :
    rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + Unit4.vec (Unit4.mulI (firstUnit t t')) ∈ tileShape (vtileOf t) ∨
    rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + Unit4.vec (Unit4.mulI (firstUnit t t')) - rotI (incr t') ∈
      tileShape (vtileOf t') := by
  simp only [ValidPair] at hv
  cases t <;> cases t' <;> first | exact (hv (by decide)).elim | decide

theorem vtl_head (t : ZTile) (ts : List ZTile) (o : GInt) :
    ∃ R, vtl (t :: ts) o = (vtileOf t, o) :: R := by
  cases ts with
  | nil => exact ⟨[], rfl⟩
  | cons t' ts => exact ⟨_, rfl⟩

theorem walk_head_mem (c : GInt) (w : F2Word) : c ∈ F2Word.walk c w := by
  unfold F2Word.walk
  cases w <;> simp [List.scanl]

theorem tileCovers_of_left (L M : List (ZTile × GInt)) (z : GInt) (h : tileCovers L z) :
    tileCovers (L ++ M) z := by
  induction L with
  | nil => exact absurd h (tileCovers_nil' z)
  | cons a L ih =>
    rw [tileCovers_cons'] at h
    rw [List.cons_append, tileCovers_cons']
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ih h)

theorem tileCovers_of_right (L M : List (ZTile × GInt)) (z : GInt) (h : tileCovers M z) :
    tileCovers (L ++ M) z := by
  induction L with
  | nil => simpa using h
  | cons a L ih => rw [List.cons_append, tileCovers_cons']; exact Or.inr ih

theorem tileCovers_of_shape (a : ZTile × GInt) (M : List (ZTile × GInt)) (z : GInt)
    (h : z ∈ (tileShape a.1).map (· + a.2)) : tileCovers (a :: M) z :=
  (tileCovers_cons' a M z).2 (Or.inl h)

/-- The predecessor tile of a pair: its vertical tile at the origin of the pair minus the step of the next tile. -/
def predL (pr : Option ZTile) (o : GInt) (t : ZTile) : List (ZTile × GInt) :=
  match pr with
  | none => []
  | some p => [(vtileOf p, o - rotI (incr t))]

/-- **The rotated chain is covered by the vertical tile list.** From the start `o + rotI (anchor t) + (1,0)`, every point of the
rotated walk of the chain, followed by its final `i`, lies in the vertical tile list (with the predecessor tile `pr`). -/
theorem cover_chain (rest : List ZTile) : ∀ (t : ZTile) (o : GInt) (pr : Option ZTile),
    ValidChain (t :: rest) → (t :: rest).getLast? = some ZTile.zero →
    (∀ p, pr = some p → ValidPair p t) →
    (pr = none → rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) ∈ tileShape (vtileOf t)) →
    ∀ z ∈ F2Word.walk (o + rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ))) (chainMV (t :: rest) ++ [Unit4.i]),
      tileCovers (predL pr o t ++ vtl (t :: rest) o) z := by
  induction rest with
  | nil =>
    intro t o pr _ hL _ _ z hz
    have ht : t = ZTile.zero := by simpa using hL
    subst ht
    have hz' : z ∈ F2Word.walk (o + rotI (anchorOff ZTile.zero) + ((1 : ℤ), (0 : ℤ))) [Unit4.i] := by
      simpa [chainMV] using hz
    rw [WalkDecomp.walk_cons, WalkDecomp.walk_nil] at hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    apply tileCovers_of_right
    apply tileCovers_of_shape
    simp only [vtileOf, List.mem_map]
    rcases hz' with rfl | rfl
    · exact ⟨((1 : ℤ), (0 : ℤ)), by decide, by simp [anchorOff, rotI]; abel⟩
    · exact ⟨((1 : ℤ), (1 : ℤ)), by decide, by
        rw [show rotI (anchorOff ZTile.zero) = ((0 : ℤ), (0 : ℤ)) from rfl,
          show Unit4.vec Unit4.i = ((0 : ℤ), (1 : ℤ)) from rfl]
        ext <;> simp <;> ring⟩
  | cons t' rest ih =>
    intro t o pr hC hL hpr hnone z hz
    have hC2 : ValidPair t t' ∧ ValidChain (t' :: rest) := hC
    obtain ⟨hv, hC'⟩ := hC2
    have hL' : (t' :: rest).getLast? = some ZTile.zero := by simpa using hL
    obtain ⟨g0, g1, hg⟩ := gPair_two t t' hv
    have hfirst : firstUnit t t' = g0 := by simp [firstUnit, hg]
    have hsum := sum_gPair t t' hv
    have hs' : o + rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + F2Word.sum ((gPair t t').map Unit4.mulI) =
        (o + rotI (incr t')) + rotI (anchorOff t') + ((1 : ℤ), (0 : ℤ)) := by
      rw [F2Word_sum_map_mulI, hsum, rotI_sub, rotI_add]
      abel
    have hsplit : chainMV (t :: t' :: rest) ++ [Unit4.i] =
        (gPair t t').map Unit4.mulI ++ (chainMV (t' :: rest) ++ [Unit4.i]) := by
      rw [chainMV_cons2, List.append_assoc]
    have hpr' : ∀ p, some t = some p → ValidPair p t' := by
      intro p hp
      have hpt : t = p := Option.some.inj hp
      exact hpt ▸ hv
    have hnone' : some t = none → rotI (anchorOff t') + ((1 : ℤ), (0 : ℤ)) ∈ tileShape (vtileOf t') :=
      fun h => absurd h (by simp)
    have IH := ih t' (o + rotI (incr t')) (some t) hC' hL' hpr' hnone'
    have hpred : predL (some t) (o + rotI (incr t')) t' = [(vtileOf t, o)] := by
      simp [predL]
    rw [hpred] at IH
    have hkey : o + rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + Unit4.vec (Unit4.mulI g0) + Unit4.vec (Unit4.mulI g1) =
        (o + rotI (incr t')) + rotI (anchorOff t') + ((1 : ℤ), (0 : ℤ)) := by
      rw [← hs', hg]
      simp [F2Word.sum]
      abel
    rw [hsplit, WalkDecomp.walk_append, hs'] at hz
    rw [hg] at hz
    simp only [List.map_cons, List.map_nil] at hz
    show tileCovers (predL pr o t ++ ((vtileOf t, o) :: vtl (t' :: rest) (o + rotI (incr t')))) z
    rcases List.mem_append.1 hz with hz1 | hz2
    · rw [WalkDecomp.walk_cons, WalkDecomp.walk_cons, WalkDecomp.walk_nil] at hz1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz1
      rcases hz1 with rfl | rfl | rfl
      · -- the start point
        rcases pr with _ | p
        · apply tileCovers_of_right
          apply tileCovers_of_shape
          exact List.mem_map.2 ⟨_, hnone rfl, by dsimp only; abel⟩
        · rcases win_start p t (hpr p rfl) with h1 | h1
          · apply tileCovers_of_right
            apply tileCovers_of_shape
            exact List.mem_map.2 ⟨_, h1, by dsimp only; abel⟩
          · show tileCovers ([(vtileOf p, o - rotI (incr t))] ++
                ((vtileOf t, o) :: vtl (t' :: rest) (o + rotI (incr t')))) _
            apply tileCovers_of_left
            apply tileCovers_of_shape
            exact List.mem_map.2 ⟨_, h1, by dsimp only; abel⟩
      · -- the middle point
        have hm := win_mid t t' hv
        rw [hfirst] at hm
        apply tileCovers_of_right
        obtain ⟨R, hR⟩ := vtl_head t' rest (o + rotI (incr t'))
        rcases hm with h1 | h1
        · apply tileCovers_of_shape
          exact List.mem_map.2 ⟨_, h1, by dsimp only; abel⟩
        · rw [hR, tileCovers_cons']
          right
          apply tileCovers_of_shape
          exact List.mem_map.2 ⟨_, h1, by dsimp only; abel⟩
      · -- the end point: the start of the tail, covered by the induction hypothesis
        have hz3 : o + rotI (anchorOff t) + ((1 : ℤ), (0 : ℤ)) + Unit4.vec (Unit4.mulI g0) +
            Unit4.vec (Unit4.mulI g1) ∈ F2Word.walk ((o + rotI (incr t')) + rotI (anchorOff t') + ((1 : ℤ), (0 : ℤ)))
              (chainMV (t' :: rest) ++ [Unit4.i]) := by
          rw [hkey]
          exact walk_head_mem _ _
        apply tileCovers_of_right
        exact IH _ hz3
    · -- the tail: the induction hypothesis at the next tile
      have hz3 := List.mem_of_mem_tail hz2
      apply tileCovers_of_right
      exact IH z hz3

/-! ### The tile sequence of a horizontal word, and S3 for the odd child -/

theorem validChain_tileSeqAux : ∀ (w : BinaryWord) (pr : Option Letter), ValidChain (tileSeqAux pr w) := by
  intro w
  induction w with
  | nil => intro pr; simp [tileSeqAux, ValidChain]
  | cons x w ih =>
    intro pr
    cases w with
    | nil => simp [tileSeqAux, ValidChain]
    | cons y w' =>
      rw [tileSeqAux_cons pr x (y :: w')]
      have h2 := ih (some x)
      rw [tileSeqAux_cons (some x) y w'] at h2
      rw [tileSeqAux_cons (some x) y w']
      exact ⟨validPair_zTileOf pr x y, h2⟩

theorem lastZero_tileSeqAux : ∀ (w : BinaryWord) (pr : Option Letter),
    w.getLast? = some Letter.p → (tileSeqAux pr w).getLast? = some ZTile.zero := by
  intro w
  induction w with
  | nil => intro pr hl; simp at hl
  | cons x w ih =>
    intro pr hl
    cases w with
    | nil =>
      have hx : x = Letter.p := by simpa using hl
      subst hx
      simp [tileSeqAux]
    | cons y w' =>
      rw [tileSeqAux_cons pr x (y :: w'), tileSeqAux_cons (some x) y w']
      have hl' : (y :: w').getLast? = some Letter.p := by simpa using hl
      rw [List.getLast?_cons_cons]
      have h2 := ih (some x) hl'
      rw [tileSeqAux_cons (some x) y w'] at h2
      exact h2

theorem gH_mulI (h : BinaryWord) : (gH h).map Unit4.mulI = chainMV (tileSeqAux none h) ++ [Unit4.i] := by
  rw [gH_unfold]
  simp only [List.map_append, List.map_cons, List.map_nil, chainOf, chainMV, List.map_flatMap, tileSeq]
  rfl

theorem head_cons_of_head (H : BinaryWord) (hd : H.head? = some Letter.q) : ∃ h', H = Letter.q :: h' := by
  cases H with
  | nil => simp at hd
  | cons x t =>
    have hx : x = Letter.q := by simpa using hd
    subst hx
    exact ⟨t, rfl⟩

/-- **The core covering.** For a horizontal word `q :: h'` ending in `p`, the rotated walk of its `gH` from `o + (1,0)` is covered by
the vertical string of the flipped word at `o`. -/
theorem core_cover (H : BinaryWord) (hd : H.head? = some Letter.q) (hl : H.getLast? = some Letter.p) (o : GInt)
    (z : GInt) (hz : z ∈ F2Word.walk (o + ((1 : ℤ), (0 : ℤ))) (chainMV (tileSeqAux none H) ++ [Unit4.i])) :
    tileCovers (vStringAt (flipW H) o) z := by
  obtain ⟨h', rfl⟩ := head_cons_of_head H hd
  rw [vStringAt_flip, tileSeqAux_cons none Letter.q h']
  have hz' : z ∈ F2Word.walk (o + rotI (anchorOff (zTileOf none Letter.q)) + ((1 : ℤ), (0 : ℤ)))
      (chainMV (zTileOf none Letter.q :: tileSeqAux (some Letter.q) h') ++ [Unit4.i]) := by
    have e : rotI (anchorOff (zTileOf none Letter.q)) = ((0 : ℤ), (0 : ℤ)) := rfl
    have hs : o + rotI (anchorOff (zTileOf none Letter.q)) + ((1 : ℤ), (0 : ℤ)) = o + ((1 : ℤ), (0 : ℤ)) := by
      rw [e]; simp
    rw [hs]
    rw [tileSeqAux_cons none Letter.q h'] at hz
    exact hz
  have hlast : (zTileOf none Letter.q :: tileSeqAux (some Letter.q) h').getLast? = some ZTile.zero := by
    have := lastZero_tileSeqAux (Letter.q :: h') none hl
    rw [tileSeqAux_cons none Letter.q h'] at this
    exact this
  have hcov := cover_chain (tileSeqAux (some Letter.q) h') (zTileOf none Letter.q) o none
    (validChain_tileSeqAux (Letter.q :: h') none) hlast (fun p hp => absurd hp (by simp))
    (fun _ => by decide) z hz'
  simpa [predL, vtl] using hcov

/-! ### S3 for both children -/

/-- **S3, odd child.** The right walk of the odd tile is covered by its vertical string (the statement used by the vertical
consumers, the reduction of the walk to the core covering). -/
theorem S3_odd (w : Word) : ∀ z ∈ F2Word.walk (F2Word.sum (oddBottom w)) (oddRight w),
    tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z := by
  intro z hz
  have hd := (FLatticePaper.Tiles.hWordOf_head_last (swapW w) true).1
  have hl := (FLatticePaper.Tiles.hWordOf_head_last (swapW w) true).2
  have hvw : vWordOf w false = flipW (hWordOf (swapW w) true) := by
    rw [← flipW_flipW (vWordOf w false), flipW_vWordOf]
    rfl
  have hrot : oddRight w = (gH (hWordOf (swapW w) true)).map Unit4.mulI := by
    rw [oddRight_eq_gV, gV]
    exact congrArg (fun u => (gH u).map Unit4.mulI) (flipW_vWordOf w false)
  have hlp : lastPosOf (hStringAt (hWordOf w false) 0) = F2Word.sum (oddBottom w) - ((1 : ℤ), (0 : ℤ)) := by
    have h : lastPosOf (hStringAt (hWordOf w false) 0) = almostV₁ (oddBottom w) - ((1 : ℤ), (1 : ℤ)) :=
      FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_false w
    rw [h]
    unfold almostV₁ gI
    ext <;> simp
  rw [hrot, gH_mulI] at hz
  rw [hvw, hlp]
  have hz' : z ∈ F2Word.walk ((F2Word.sum (oddBottom w) - ((1 : ℤ), (0 : ℤ))) + ((1 : ℤ), (0 : ℤ)))
      (chainMV (tileSeqAux none (hWordOf (swapW w) true)) ++ [Unit4.i]) := by
    rw [sub_add_cancel]
    exact hz
  exact core_cover _ hd hl _ z hz'

/-- **S3, even child.** The right walk of the even tile is covered by its vertical string. -/
theorem S3_even (w : Word) : ∀ z ∈ F2Word.walk (F2Word.sum (evenBottom w)) (evenRight w),
    tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z := by
  intro z hz
  have hd := (FLatticePaper.Tiles.hWordOf_head_last (swapW w) false).1
  have hl := (FLatticePaper.Tiles.hWordOf_head_last (swapW w) false).2
  have hvw : vWordOf w true = flipW (hWordOf (swapW w) false) := by
    rw [← flipW_flipW (vWordOf w true), flipW_vWordOf]
    rfl
  have hrot : evenRight w = (gH (hWordOf (swapW w) false)).map Unit4.mulI := by
    rw [evenRight_eq_gV, gV]
    exact congrArg (fun u => (gH u).map Unit4.mulI) (flipW_vWordOf w true)
  have hlp : lastPosOf (hStringAt (hWordOf w true) 0) = F2Word.sum (evenBottom w) - ((1 : ℤ), (0 : ℤ)) := by
    have h : lastPosOf (hStringAt (hWordOf w true) 0) = almostV₁ (evenBottom w) - ((1 : ℤ), (1 : ℤ)) :=
      FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_true w
    rw [h]
    unfold almostV₁ gI
    ext <;> simp
  rw [hrot, gH_mulI] at hz
  rw [hvw, hlp]
  have hz' : z ∈ F2Word.walk ((F2Word.sum (evenBottom w) - ((1 : ℤ), (0 : ℤ))) + ((1 : ℤ), (0 : ℤ)))
      (chainMV (tileSeqAux none (hWordOf (swapW w) false)) ++ [Unit4.i]) := by
    rw [sub_add_cancel]
    exact hz
  exact core_cover _ hd hl _ z hz'


end FLatticePaper.Tiles.VerticalCover


