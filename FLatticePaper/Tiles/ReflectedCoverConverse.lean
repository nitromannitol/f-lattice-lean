import FLatticePaper.Tiles.StdPseudoAnchoredSets
import FLatticePaper.Tiles.VertStringReflect
import FLatticePaper.Tiles.StdHalfTurnCentre
import FLatticePaper.Tiles.StdCornerAnchors

/-! # The reflected covering, converse: the reversed horizontal string reflects into the forward one

`ReflectedCover.cover_reflect` sends a point covered by the forward tile list of a word `h` (last letter `e`) to a point covered by
the reversed tile list started at `c`, through the centre `c + lastPos + shR e`. This file proves the other inclusion, so that the
two placed sets are exchanged by the half-turn (`placed_hRev_iff`). The vertical analogue is the placed-set form of the list identity
`VertStringReflect.vRev_reflect_gen` (`placed_vRev_iff`). For the anchored strings of the standard tiles the two give the half-turn
identities of `IsPseudoSquareAnchoredPt` about `halfTurnCentre T` (`hRev_halfTurn_odd`, `_even`, `vFwd_halfTurn_odd`, `_even`).

The correspondence is not tile by tile: an enlarged tile `T^d_{1/1}` of the forward string is the second `q` of a pair `qq`, while
in the reversed string it is the first `q` of that pair (in forward order). The two tips `(-1, 1)`, `(1, -1)` of the reversed
enlarged tile at the forward index `m` reflect to `P_m + (2, 0)`, `P_m + (0, 2)`, which are the tips of the forward enlarged tile at
`m + 1` (`P_{m+1} = P_m + (1, 1)`). The induction appends a letter to the word (which prepends it to the reversed word, whose tail
then has the predecessor of that letter); the statement carries, for the predecessor `q` and the last letter `q`, the two reflected
tips, which are covered only once the next forward tile is there (`rev_reflect`). -/

namespace FLatticePaper.Tiles.ReflectedCoverConverse

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.HBottom
open FLatticePaper.Tiles.ReflectedCover

/-- A point of the enlarged tile is a point of `T_{1/1}` or one of the two tips. -/
theorem oneD_cases (s : GInt) (hs : s ∈ tileShape ZTile.oneD) :
    s ∈ tileShape ZTile.one ∨ s = ((-1 : ℤ), (1 : ℤ)) ∨ s = ((1 : ℤ), (-1 : ℤ)) := by
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem tip1_mem : ((1 : ℤ), (-1 : ℤ)) ∈ tileShape ZTile.oneD := by simp [tileShape]

theorem tip2_mem : ((-1 : ℤ), (1 : ℤ)) ∈ tileShape ZTile.oneD := by simp [tileShape]

/-- The head tile of the reversed list, reflected: a point of `zTileOf pr x` at `c` goes to `K - s` with `K = P + shR x`; it is in
the tile `t` at `P` of letter `x` (any predecessor for `q`), unless it is a tip of an enlarged reversed tile. -/
theorem head_reflect (pr : Option Letter) (x : Letter) (t : ZTile) (ht : t = zTileOf pr' x) (s P : GInt)
    (hs : s ∈ tileShape (zTileOf pr x)) :
    P + shR x - s ∈ (tileShape t).map (· + P) ∨
      (pr = some Letter.q ∧ x = Letter.q ∧
        (P + shR x - s = P + ((2 : ℤ), (0 : ℤ)) ∨ P + shR x - s = P + ((0 : ℤ), (2 : ℤ)))) := by
  subst ht
  cases x with
  | p =>
    left
    simp only [List.mem_map]
    exact ⟨(1, 2) - s, by simpa [zTileOf] using refl_p s (by simpa [zTileOf] using hs), by simp only [shR]; abel⟩
  | q =>
    rcases pr with _ | ⟨_ | _⟩
    · left
      simp only [List.mem_map]
      exact ⟨(1, 1) - s, R2_sub pr' _ (refl_q s (by simpa [zTileOf] using hs)), by simp only [shR]; abel⟩
    · left
      simp only [List.mem_map]
      exact ⟨(1, 1) - s, R2_sub pr' _ (refl_q s (by simpa [zTileOf] using hs)), by simp only [shR]; abel⟩
    · rcases oneD_cases s (by simpa [zTileOf] using hs) with h1 | rfl | rfl
      · left
        simp only [List.mem_map]
        exact ⟨(1, 1) - s, R2_sub pr' _ (refl_q s h1), by simp only [shR]; abel⟩
      · right
        refine ⟨rfl, rfl, Or.inl ?_⟩
        simp only [shR]
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
      · right
        refine ⟨rfl, rfl, Or.inr ?_⟩
        simp only [shR]
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega

/-- **The converse of the reflected covering.** A point covered by the reversed tile list of `h` (predecessor `pr`, start `c`) is
reflected through `c + lastPos + shR e` to a point covered by the forward tile list of `h`, except, when the predecessor and the
last letter are both `q`, for the two reflected tips `lastPos + (2, 0)`, `lastPos + (0, 2)` of the enlarged head. -/
theorem rev_reflect (h : BinaryWord) :
    ∀ (e : Letter) (pr : Option Letter) (c y : GInt), h.getLast? = some e →
      tileCovers (revTiles pr h.reverse c) y →
      tileCovers (fwdTiles none h 0) (c + lastPosOf (fwdTiles none h 0) + shR e - y) ∨
        (pr = some Letter.q ∧ e = Letter.q ∧
          (c + lastPosOf (fwdTiles none h 0) + shR e - y = lastPosOf (fwdTiles none h 0) + ((2 : ℤ), (0 : ℤ)) ∨
            c + lastPosOf (fwdTiles none h 0) + shR e - y = lastPosOf (fwdTiles none h 0) + ((0 : ℤ), (2 : ℤ)))) := by
  induction h using List.reverseRecOn with
  | nil => intro e pr c y he; simp at he
  | append_singleton L x ih =>
    intro e pr c y he hy
    have hx : x = e := by simpa using he
    subst hx
    rcases List.eq_nil_or_concat L with rfl | ⟨M, y', rfl⟩
    · -- the single letter `x`
      simp only [List.nil_append, List.reverse_singleton] at hy ⊢
      rw [revTiles_single, tileCovers_cons'] at hy
      simp only [tileCovers_nil', or_false, List.mem_map] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      have hp : lastPosOf (fwdTiles none [x] 0) = 0 := by rw [fwdTiles_single]; simp [lastPosOf]
      rw [hp, fwdTiles_single, tileCovers_cons']
      simp only [tileCovers_nil', or_false]
      have key := head_reflect (pr' := none) pr x (zTileOf none x) rfl s 0 hs
      have e1 : c + 0 + shR x - (s + c) = 0 + shR x - s := by abel
      rw [e1]
      simpa using key
    · -- the step: the letter `x` after the word `M ++ [y']`
      simp only [List.concat_eq_append] at ih hy ⊢
      have hl : (M ++ [y']).getLast? = some y' := by simp
      have hfa := fwdTiles_append (M ++ [y']) none 0 x (by simp)
      rw [hl] at hfa
      have hlp : lastPosOf (fwdTiles none ((M ++ [y']) ++ [x]) 0)
          = lastPosOf (fwdTiles none (M ++ [y']) 0) + hOffset x := by
        rw [hfa, lastPos_append_single]
      rw [show (M ++ [y'] ++ [x]).reverse = x :: y' :: M.reverse by simp, revTiles_cons2, tileCovers_cons'] at hy
      rw [hlp, hfa, tileCovers_append_single']
      set P := lastPosOf (fwdTiles none (M ++ [y']) 0) with hP
      rcases hy with hA | hB
      · -- the head tile of the reversed list
        simp only [List.mem_map] at hA
        obtain ⟨s, hs, rfl⟩ := hA
        have key := head_reflect (pr' := some y') pr x (zTileOf (some y') x) rfl s (P + hOffset x) hs
        have e1 : c + (P + hOffset x) + shR x - (s + c) = P + hOffset x + shR x - s := by abel
        rw [e1]
        rcases key with k | k
        · exact Or.inl (Or.inr k)
        · exact Or.inr k
      · -- the tail: the induction hypothesis with the predecessor `x`
        have IH := ih y' (some x) (c + hRevOffset x y') y (by simp)
          (by rw [show (M ++ [y']).reverse = y' :: M.reverse by simp]; exact hB)
        have hpt : c + (P + hOffset x) + shR x - y = c + hRevOffset x y' + P + shR y' - y := by
          rw [offset_identity]; abel
        rw [hpt]
        rcases IH with k | ⟨hxq, hyq, k⟩
        · exact Or.inl (Or.inl k)
        · -- the reflected tips of the enlarged reversed tile: tips of the new forward tile
          have hxq' : x = Letter.q := by simpa using hxq
          subst hxq' hyq
          left; right
          simp only [List.mem_map]
          rcases k with k | k
          · refine ⟨((1 : ℤ), (-1 : ℤ)), by simpa [zTileOf] using tip1_mem, ?_⟩
            rw [k]; simp only [hOffset]; refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
          · refine ⟨((-1 : ℤ), (1 : ℤ)), by simpa [zTileOf] using tip2_mem, ?_⟩
            rw [k]; simp only [hOffset]; refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- The reversed horizontal string reflects into the forward one. -/
theorem rev_into_fwd (h : BinaryWord) (e : Letter) (he : h.getLast? = some e) (c x : GInt)
    (hx : x ∈ placedSites (hRevStringAt h.reverse c)) :
    c + lastPosOf (hStringAt h (0, 0)) + shR e - x ∈ placedSites (hStringAt h (0, 0)) := by
  rw [StdPseudoAnchoredSets.mem_placedSites_iff_tileCovers] at hx ⊢
  have := rev_reflect h e none c x he hx
  rcases this with k | ⟨hc, -⟩
  · exact k
  · exact absurd hc (by simp)

/-- **The half-turn of the horizontal strings.** The placed set of the reversed horizontal string of `h` at `c` is the reflection of
the placed set of the forward horizontal string at the origin through `c + lastPos + shR e`. -/
theorem placed_hRev_iff (h : BinaryWord) (e : Letter) (he : h.getLast? = some e) (c x : GInt) :
    x ∈ placedSites (hRevStringAt h.reverse c) ↔
      c + lastPosOf (hStringAt h (0, 0)) + shR e - x ∈ placedSites (hStringAt h (0, 0)) := by
  refine ⟨rev_into_fwd h e he c x, fun hz => ?_⟩
  rw [StdPseudoAnchoredSets.mem_placedSites_iff_tileCovers] at hz ⊢
  have := cover_reflect h e none c _ he hz
  have e1 : c + lastPosOf (fwdTiles none h 0) + shR e - (c + lastPosOf (hStringAt h (0, 0)) + shR e - x) = x := by
    show c + lastPosOf (hStringAt h (0, 0)) + shR e - (c + lastPosOf (hStringAt h (0, 0)) + shR e - x) = x
    abel
  rw [e1] at this
  exact this

/-! ### The vertical strings -/

theorem shape_refl_letter (x : Letter) (s : GInt) (hs : s ∈ tileShape (letterZTile x)) :
    VertStringReflect.sT (letterZTile x) - s ∈ tileShape (letterZTile x) := by
  cases x
  · exact refl_p s hs
  · exact refl_q s hs

theorem vString_tiles (w : BinaryWord) (a : GInt) (t : ZTile × GInt) (ht : t ∈ vStringAt w a) :
    ∃ x : Letter, t.1 = letterZTile x := by
  unfold vStringAt at ht
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  simp only [List.getElem_zip, List.getElem_map]
  exact ⟨_, rfl⟩

/-- **The half-turn of the vertical strings.** The placed set of the reversed vertical string of `w` (last letter `x`) at `c` is the
reflection of the placed set of the forward vertical string at `a` through `a + lastPos + shR x + c`
(`VertStringReflect.vRev_reflect_gen`). -/
theorem placed_vRev_iff (w : BinaryWord) (x : Letter) (hx : w.getLast? = some x) (a c z : GInt) :
    z ∈ placedSites (vRevStringAt w.reverse c) ↔
      a + lastPosOf (vStringAt w (0, 0)) + shR x + c - z ∈ placedSites (vStringAt w a) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v ++ [x] := ⟨w.dropLast, (List.dropLast_append_getLast? _ hx).symm⟩
  rw [VertStringReflect.vRev_reflect_gen v x a c]
  unfold placedSites
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, s, hs, rfl⟩
    obtain ⟨y, hy⟩ := vString_tiles _ _ t ht
    refine ⟨t, ht, VertStringReflect.sT t.1 - s, ?_, ?_⟩
    · rw [hy] at hs ⊢; exact shape_refl_letter y s hs
    · refine Prod.ext ?_ ?_ <;> simp <;> ring
  · rintro ⟨t, ht, s, hs, hz⟩
    obtain ⟨y, hy⟩ := vString_tiles _ _ t ht
    refine ⟨_, ⟨t, ht, rfl⟩, VertStringReflect.sT t.1 - s, ?_, ?_⟩
    · rw [hy] at hs ⊢; exact shape_refl_letter y s hs
    · have hz' := congrArg (fun q : GInt => a + lastPosOf (vStringAt (v ++ [x]) (0, 0)) + shR x + c - q) hz
      simp only [sub_sub_cancel] at hz'
      rw [← hz']
      refine Prod.ext ?_ ?_ <;> simp <;> ring

/-! ### The half-turn identities of the anchored strings of the standard tiles

For the anchored strings of `IsPseudoSquareAnchoredPt` at `c(T) = 0` (`anchoredStrings wh wv 0`: the forward horizontal string at
`0`, the reversed vertical string at `0`, the forward vertical string at `s_v = lastPos(H^+)` and the reversed horizontal string at
`s_h = lastPos(V^-)`), the reversed horizontal string is the half-turn of the forward horizontal one and the forward vertical
string the half-turn of the reversed vertical one, about the half-turn centre `C = v_1 + v_2 + 1 - i` of the tile
(`StdHalfTurnCentre`): `x ↦ C - x`. -/

open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf halfTurnCentre)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.Standard (oddTile evenTile)

theorem centre_odd_eq (w : Word) :
    lastPosOf (vRevStringAt (vWordOf w false).reverse (0, 0)) + lastPosOf (hStringAt (hWordOf w false) (0, 0)) + shR .p =
      halfTurnCentre (oddTile w) := by
  rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, StdCornerAnchors.stdAnchorY_odd, StdHalfTurnCentre.stdCentre_odd,
    show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd]
  simp only [shR]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem centre_even_eq (w : Word) :
    lastPosOf (vRevStringAt (vWordOf w true).reverse (0, 0)) + lastPosOf (hStringAt (hWordOf w true) (0, 0)) + shR .p =
      halfTurnCentre (evenTile w) := by
  rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, StdCornerAnchors.stdAnchorY_even, StdHalfTurnCentre.stdCentre_even,
    show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_even]
  simp only [shR]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem vcentre_odd_eq (w : Word) :
    lastPosOf (hStringAt (hWordOf w false) (0, 0)) + lastPosOf (vStringAt (vWordOf w false) (0, 0)) + shR .q =
      halfTurnCentre (oddTile w) := by
  rw [StdCornerAnchors.stdAnchorX_odd, StdHalfTurnCentre.stdCentre_odd,
    StdCornerAnchors.stdAnchorC_of (vWordOf w false) (fracOdd w).num (fracOdd w).den
      (StringCorners.vertWord_head_last w).1 (vertWord_counts w).1 (vertWord_counts w).2]
  simp only [shR, Construction.texV1Odd, Construction.texV2]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega

theorem vcentre_even_eq (w : Word) :
    lastPosOf (hStringAt (hWordOf w true) (0, 0)) + lastPosOf (vStringAt (vWordOf w true) (0, 0)) + shR .q =
      halfTurnCentre (evenTile w) := by
  rw [StdCornerAnchors.stdAnchorX_even, StdHalfTurnCentre.stdCentre_even,
    StdCornerAnchors.stdAnchorC_of (vWordOf w true) (fracEven w).num (fracEven w).den
      (StringCorners.vWord_even_head_last w).1 (StringCorners.vWord_even_counts w).1 (StringCorners.vWord_even_counts w).2]
  simp only [shR, Construction.texV1Even, Construction.texV2]
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega

/-- (H) for the odd child: the reversed horizontal string at `s_h` is the half-turn of the forward horizontal string at `0`. -/
theorem hRev_halfTurn_odd (w : Word) (x : GInt) :
    x ∈ placedSites (hRevStringAt (hWordOf w false).reverse (lastPosOf (vRevStringAt (vWordOf w false).reverse (0, 0)))) ↔
      halfTurnCentre (oddTile w) - x ∈ placedSites (hStringAt (hWordOf w false) (0, 0)) := by
  rw [placed_hRev_iff _ Letter.p (hWordOf_head_last w false).2, centre_odd_eq]

/-- (H) for the even child. -/
theorem hRev_halfTurn_even (w : Word) (x : GInt) :
    x ∈ placedSites (hRevStringAt (hWordOf w true).reverse (lastPosOf (vRevStringAt (vWordOf w true).reverse (0, 0)))) ↔
      halfTurnCentre (evenTile w) - x ∈ placedSites (hStringAt (hWordOf w true) (0, 0)) := by
  rw [placed_hRev_iff _ Letter.p (hWordOf_head_last w true).2, centre_even_eq]

/-- (V) for the odd child: the forward vertical string at `s_v` is the half-turn of the reversed vertical string at `0`. -/
theorem vFwd_halfTurn_odd (w : Word) (x : GInt) :
    x ∈ placedSites (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) (0, 0)))) ↔
      halfTurnCentre (oddTile w) - x ∈ placedSites (vRevStringAt (vWordOf w false).reverse (0, 0)) := by
  rw [placed_vRev_iff (vWordOf w false) Letter.q (by exact (StringCorners.vertWord_head_last w).2)
    (lastPosOf (hStringAt (hWordOf w false) (0, 0))) (0, 0), ← vcentre_odd_eq]
  have e : lastPosOf (hStringAt (hWordOf w false) (0, 0)) + lastPosOf (vStringAt (vWordOf w false) (0, 0)) + shR Letter.q +
      ((0 : ℤ), (0 : ℤ)) - (lastPosOf (hStringAt (hWordOf w false) (0, 0)) + lastPosOf (vStringAt (vWordOf w false) (0, 0)) +
        shR Letter.q - x) = x := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, add_zero, sub_sub_cancel]
  rw [e]

/-- (V) for the even child. -/
theorem vFwd_halfTurn_even (w : Word) (x : GInt) :
    x ∈ placedSites (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) (0, 0)))) ↔
      halfTurnCentre (evenTile w) - x ∈ placedSites (vRevStringAt (vWordOf w true).reverse (0, 0)) := by
  rw [placed_vRev_iff (vWordOf w true) Letter.q (by exact (StringCorners.vWord_even_head_last w).2)
    (lastPosOf (hStringAt (hWordOf w true) (0, 0))) (0, 0), ← vcentre_even_eq]
  have e : lastPosOf (hStringAt (hWordOf w true) (0, 0)) + lastPosOf (vStringAt (vWordOf w true) (0, 0)) + shR Letter.q +
      ((0 : ℤ), (0 : ℤ)) - (lastPosOf (hStringAt (hWordOf w true) (0, 0)) + lastPosOf (vStringAt (vWordOf w true) (0, 0)) +
        shR Letter.q - x) = x := by
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : GInt) from rfl, add_zero, sub_sub_cancel]
  rw [e]

end FLatticePaper.Tiles.ReflectedCoverConverse
