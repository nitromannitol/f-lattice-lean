import FLatticePaper.Tiles.HBottom
import FLatticePaper.Tiles.ClosedWalkVertical
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! The reflected covering of a forward horizontal string (the top side of the translate of a tile, S1 of the overlap form of H2).

For a forward word `h` with last letter `e`, the forward tile list `fwdTiles none h 0` covers a point `z`; then the reversed tile list
`revTiles pr h.reverse c` covers `c + lastPos + shR e - z`, where `lastPos` is the origin of the last forward tile and `shR e` is
`(1,2)` for `p` and `(1,1)` for `q`. The induction appends a letter to `h`, which prepends it to the reversed word; the predecessor
letter `pr` of the reversed word is then generalised. An enlarged forward tile has two tips, which are covered by the next reversed
tile (`oneD`), exactly when the letters match. -/

namespace FLatticePaper.Tiles.ReflectedCover

open FLatticePaper.Tiles FLatticePaper.Tiles.HBottom FLatticePaper.Farey

/-- The reflection shift of the last letter: `(1,2)` for `p`, `(1,1)` for `q`. -/
def shR : Letter → GInt
  | .p => (1, 2)
  | .q => (1, 1)

/-- The forward tile list from a predecessor and a start (the list `hStringAt` for `pr = none`). -/
def fwdTiles (pr : Option Letter) (w : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (tileSeqAux pr w).zip (List.scanl (· + ·) c (w.tail.map hOffset))

/-- The reversed tile list from a predecessor and a start (the list `hRevStringAt` for `pr = none`). -/
def revTiles (pr : Option Letter) (u : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (tileSeqAux pr u).zip (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2))

theorem offset_identity (x y : Letter) : hRevOffset x y = hOffset x + shR x - shR y := by
  cases x <;> cases y <;> decide

theorem tileCovers_nil' (z : GInt) : ¬ tileCovers [] z := by
  unfold tileCovers
  simp

theorem tileCovers_cons' (a : ZTile × GInt) (L : List (ZTile × GInt)) (z : GInt) :
    tileCovers (a :: L) z ↔ z ∈ (tileShape a.1).map (· + a.2) ∨ tileCovers L z := by
  unfold tileCovers
  constructor
  · rintro ⟨k, hk, hz⟩
    cases k with
    | zero => exact Or.inl (by simpa using hz)
    | succ k => exact Or.inr ⟨k, by simpa using hk, by simpa using hz⟩
  · rintro (h | ⟨k, hk, hz⟩)
    · exact ⟨0, by simp, by simpa using h⟩
    · exact ⟨k + 1, by simpa using hk, by simpa using hz⟩

theorem tileCovers_append_single' (L : List (ZTile × GInt)) (a : ZTile × GInt) (z : GInt) :
    tileCovers (L ++ [a]) z ↔ tileCovers L z ∨ z ∈ (tileShape a.1).map (· + a.2) := by
  induction L with
  | nil => simp [tileCovers_cons', tileCovers_nil']
  | cons b L ih =>
    rw [List.cons_append, tileCovers_cons', ih, tileCovers_cons']
    tauto

theorem fwdTiles_cons (pr : Option Letter) (x y : Letter) (w : BinaryWord) (c : GInt) :
    fwdTiles pr (x :: y :: w) c = (zTileOf pr x, c) :: fwdTiles (some x) (y :: w) (c + hOffset y) := by
  unfold fwdTiles
  simp [tileSeqAux_cons, List.scanl_cons]

theorem fwdTiles_single (pr : Option Letter) (x : Letter) (c : GInt) :
    fwdTiles pr [x] c = [(zTileOf pr x, c)] := by
  unfold fwdTiles
  simp [tileSeqAux_cons]

theorem fwdTiles_head (pr : Option Letter) (x : Letter) (w : BinaryWord) (c : GInt) :
    ∃ rest, fwdTiles pr (x :: w) c = (zTileOf pr x, c) :: rest := by
  cases w with
  | nil => exact ⟨[], fwdTiles_single pr x c⟩
  | cons y w => exact ⟨_, fwdTiles_cons pr x y w c⟩

theorem revTiles_single (pr : Option Letter) (x : Letter) (c : GInt) :
    revTiles pr [x] c = [(zTileOf pr x, c)] := by
  unfold revTiles
  simp [tileSeqAux_cons]

theorem revTiles_cons2 (pr : Option Letter) (x y : Letter) (w : BinaryWord) (c : GInt) :
    revTiles pr (x :: y :: w) c = (zTileOf pr x, c) :: revTiles (some x) (y :: w) (c + hRevOffset x y) := by
  unfold revTiles
  simp [tileSeqAux_cons, List.scanl_cons]

theorem revTiles_head (pr : Option Letter) (x : Letter) (w : BinaryWord) (c : GInt) :
    ∃ rest, revTiles pr (x :: w) c = (zTileOf pr x, c) :: rest := by
  cases w with
  | nil => exact ⟨[], revTiles_single pr x c⟩
  | cons y w => exact ⟨_, revTiles_cons2 pr x y w c⟩

theorem lastPos_cons_of_ne (a : ZTile × GInt) (T : List (ZTile × GInt)) (hT : T ≠ []) :
    lastPosOf (a :: T) = lastPosOf T := by
  cases T with
  | nil => exact absurd rfl hT
  | cons b T' => simp [lastPosOf]

theorem lastPos_append_single (L : List (ZTile × GInt)) (a : ZTile × GInt) :
    lastPosOf (L ++ [a]) = a.2 := by
  simp [lastPosOf]

theorem fwdTiles_append (w : BinaryWord) : ∀ (pr : Option Letter) (c : GInt) (x : Letter), w ≠ [] →
    fwdTiles pr (w ++ [x]) c =
      fwdTiles pr w c ++ [(zTileOf w.getLast? x, lastPosOf (fwdTiles pr w c) + hOffset x)] := by
  induction w with
  | nil => intro pr c x h; exact absurd rfl h
  | cons a w ih =>
    intro pr c x _
    cases w with
    | nil =>
      rw [show ([a] ++ [x]) = a :: x :: [] from rfl, fwdTiles_cons, fwdTiles_single, fwdTiles_single]
      simp [lastPosOf]
    | cons b w' =>
      obtain ⟨rest, hrest⟩ := fwdTiles_head (some a) b w' (c + hOffset b)
      have hT : fwdTiles (some a) (b :: w') (c + hOffset b) ≠ [] := by
        rw [hrest]; exact List.cons_ne_nil _ _
      have e2 : fwdTiles (some a) (b :: (w' ++ [x])) (c + hOffset b) =
          fwdTiles (some a) (b :: w') (c + hOffset b) ++
            [(zTileOf (b :: w').getLast? x, lastPosOf (fwdTiles (some a) (b :: w') (c + hOffset b)) + hOffset x)] :=
        ih (some a) (c + hOffset b) x (by simp)
      have e1 : (a :: b :: w') ++ [x] = a :: b :: (w' ++ [x]) := rfl
      rw [e1, fwdTiles_cons, fwdTiles_cons, e2, lastPos_cons_of_ne _ _ hT]
      simp [List.getLast?_cons_cons]

/-! ### The shapes of the tiles under the reflection -/

theorem refl_p (s : GInt) (hs : s ∈ tileShape ZTile.zero) : ((1 : ℤ), (2 : ℤ)) - s ∈ tileShape ZTile.zero := by
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem refl_q (s : GInt) (hs : s ∈ tileShape ZTile.one) : ((1 : ℤ), (1 : ℤ)) - s ∈ tileShape ZTile.one := by
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl <;> decide

theorem R2_sub (pr : Option Letter) (s : GInt) (hs : s ∈ tileShape ZTile.one) :
    s ∈ tileShape (zTileOf pr .q) := by
  rcases pr with _ | ⟨_ | _⟩
  · exact hs
  · exact hs
  · simp only [zTileOf, tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
    tauto

theorem oneD_cover (s : GInt) (hs : s ∈ tileShape ZTile.oneD) :
    ((1 : ℤ), (1 : ℤ)) - s ∈ tileShape ZTile.one ∨ -s ∈ tileShape ZTile.oneD := by
  simp only [tileShape, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### The reflected covering -/

/-- The covering of a step: a point of the new last tile of the forward word is covered by the reversed head pair, whose second tile
is `oneD` exactly when the letters match. -/
theorem stepB (pr : Option Letter) (x y : Letter) (c s : GInt) (w : BinaryWord)
    (hs : s ∈ tileShape (zTileOf (some y) x)) :
    tileCovers ((zTileOf pr x, c) :: revTiles (some x) (y :: w) (c + hRevOffset x y)) (c + shR x - s) := by
  obtain ⟨rest, hrest⟩ := revTiles_head (some x) y w (c + hRevOffset x y)
  rw [hrest, tileCovers_cons', tileCovers_cons']
  cases x <;> cases y
  · left
    simp only [List.mem_map]
    exact ⟨(1, 2) - s, refl_p s hs, by simp only [shR]; abel⟩
  · left
    simp only [List.mem_map]
    exact ⟨(1, 2) - s, refl_p s hs, by simp only [shR]; abel⟩
  · left
    simp only [List.mem_map]
    exact ⟨(1, 1) - s, R2_sub pr _ (refl_q s hs), by simp only [shR]; abel⟩
  · rcases oneD_cover s hs with h1 | h2
    · left
      simp only [List.mem_map]
      exact ⟨(1, 1) - s, R2_sub pr _ h1, by simp only [shR]; abel⟩
    · right
      left
      simp only [List.mem_map]
      exact ⟨-s, h2, by simp only [shR, hRevOffset]; abel⟩

/-- **The reflected covering.** For a forward word `h` with last letter `e`, a point covered by the forward tile list is reflected
to a point covered by the reversed tile list started at `c`, through the centre `c + lastPos + shR e`. -/
theorem cover_reflect (h : BinaryWord) :
    ∀ (e : Letter) (pr : Option Letter) (c z : GInt), h.getLast? = some e →
      tileCovers (fwdTiles none h 0) z →
      tileCovers (revTiles pr h.reverse c) (c + lastPosOf (fwdTiles none h 0) + shR e - z) := by
  induction h using List.reverseRecOn with
  | nil => intro e pr c z he; simp at he
  | append_singleton L x ih =>
    intro e pr c z he hz
    have hx : x = e := by simpa using he
    rw [← hx]
    rcases List.eq_nil_or_concat L with rfl | ⟨M, y, rfl⟩
    · -- the single letter `x`
      simp only [List.nil_append, List.reverse_singleton] at hz ⊢
      rw [fwdTiles_single, tileCovers_cons'] at hz
      simp only [tileCovers_nil', or_false] at hz
      have hp : lastPosOf (fwdTiles none [x] 0) = 0 := by
        rw [fwdTiles_single]; simp [lastPosOf]
      rw [hp, revTiles_single, tileCovers_cons']
      simp only [tileCovers_nil', or_false]
      simp only [List.mem_map] at hz ⊢
      obtain ⟨s, hs, rfl⟩ := hz
      cases x
      · exact ⟨(1, 2) - s, refl_p s hs, by simp only [shR, add_zero]; abel⟩
      · exact ⟨(1, 1) - s, R2_sub pr _ (refl_q s hs), by simp only [shR, add_zero]; abel⟩
    · -- the step: the letter `x` after the word `M ++ [y]`
      simp only [List.concat_eq_append] at ih hz ⊢
      have hl : (M ++ [y]).getLast? = some y := by simp
      have hlp : lastPosOf (fwdTiles none ((M ++ [y]) ++ [x]) 0)
          = lastPosOf (fwdTiles none (M ++ [y]) 0) + hOffset x := by
        rw [fwdTiles_append (M ++ [y]) none 0 x (by simp), lastPos_append_single]
      rw [fwdTiles_append (M ++ [y]) none 0 x (by simp), tileCovers_append_single', hl] at hz
      rw [hlp, show (M ++ [y] ++ [x]).reverse = x :: y :: M.reverse by simp, revTiles_cons2]
      rcases hz with hA | hB
      · have IH := ih y (some x) (c + hRevOffset x y) z (by simp) hA
        rw [show (M ++ [y]).reverse = y :: M.reverse by simp] at IH
        rw [tileCovers_cons']
        right
        have hpt : c + (lastPosOf (fwdTiles none (M ++ [y]) 0) + hOffset x) + shR x - z
            = c + hRevOffset x y + lastPosOf (fwdTiles none (M ++ [y]) 0) + shR y - z := by
          rw [offset_identity]; abel
        rw [hpt]; exact IH
      · obtain ⟨s, hs, hsz⟩ := List.mem_map.1 hB
        subst hsz
        have hpt : c + (lastPosOf (fwdTiles none (M ++ [y]) 0) + hOffset x) + shR x
            - (s + (lastPosOf (fwdTiles none (M ++ [y]) 0) + hOffset x)) = c + shR x - s := by abel
        rw [hpt]
        exact stepB pr x y c s M.reverse hs

end FLatticePaper.Tiles.ReflectedCover


