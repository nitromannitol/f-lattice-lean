import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.CornerPositions
import FLatticePaper.Tiles.IncrementCounts
import FLatticePaper.Tiles.SurgicalCornerThird
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.StringCorners

/-! The reflected covering of a forward vertical string (S4 of the vertical H2 hypotheses, the vertical analogue of
`ReflectedCover.cover_reflect`).

For a forward word `h` with last letter `e`, a tile list `vStringAt h c0` covers `z`; then the reversed vertical list
`vRevStringAt h.reverse c` covers `c + lastPosOf (vStringAt h c0) + shR e - z`, for every `c`. The vertical tiles are
symmetric rectangles (`p`: 2 by 3, `q`: 2 by 2), so the reflected tile is the reversed tile at the reflected position, and
no enlarged tip occurs. The offsets satisfy `vRevOffset x y = vOffset x + shR x - shR y`. -/

namespace FLatticePaper.Tiles.VerticalReflect

open FLatticePaper.Tiles FLatticePaper.Tiles.ReflectedCover FLatticePaper.Tiles.SiteStrings FLatticePaper.Farey
open FLatticePaper.Construction FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause

theorem vrev_offset_identity (x y : Letter) : vRevOffset x y = vOffset x + shR x - shR y := by
  cases x <;> cases y <;> decide

theorem vStr_cons2 (x y : Letter) (w : BinaryWord) (c : GInt) :
    vStringAt (x :: y :: w) c = (letterZTile x, c) :: vStringAt (y :: w) (c + vOffset y) := by
  simp [vStringAt, List.scanl_cons]

theorem vStr_single (x : Letter) (c : GInt) : vStringAt [x] c = [(letterZTile x, c)] := by
  simp [vStringAt]

theorem vStr_head (x : Letter) (w : BinaryWord) (c : GInt) :
    ∃ rest, vStringAt (x :: w) c = (letterZTile x, c) :: rest := by
  cases w with
  | nil => exact ⟨[], vStr_single x c⟩
  | cons y w => exact ⟨_, vStr_cons2 x y w c⟩

theorem vRev_single (x : Letter) (c : GInt) : vRevStringAt [x] c = [(letterZTile x, c)] := by
  simp [vRevStringAt]

theorem vRev_cons2 (x y : Letter) (w : BinaryWord) (c : GInt) :
    vRevStringAt (x :: y :: w) c = (letterZTile x, c) :: vRevStringAt (y :: w) (c + vRevOffset x y) := by
  simp [vRevStringAt, List.scanl_cons]

/-- Appending a letter to a forward vertical string appends the tile at the offset of that letter. -/
theorem vStr_append (w : BinaryWord) : ∀ (c : GInt) (x : Letter), w ≠ [] →
    vStringAt (w ++ [x]) c = vStringAt w c ++ [(letterZTile x, lastPosOf (vStringAt w c) + vOffset x)] := by
  induction w with
  | nil => intro c x h; exact absurd rfl h
  | cons a w ih =>
    intro c x _
    cases w with
    | nil =>
      rw [show ([a] ++ [x]) = a :: x :: [] from rfl, vStr_cons2, vStr_single, vStr_single]
      simp [lastPosOf]
    | cons b w' =>
      obtain ⟨rest, hrest⟩ := vStr_head b w' (c + vOffset b)
      have hne : vStringAt (b :: w') (c + vOffset b) ≠ [] := by
        rw [hrest]; exact List.cons_ne_nil _ _
      have e2 : vStringAt (b :: (w' ++ [x])) (c + vOffset b) =
          vStringAt (b :: w') (c + vOffset b) ++
            [(letterZTile x, lastPosOf (vStringAt (b :: w') (c + vOffset b)) + vOffset x)] :=
        ih (c + vOffset b) x (by simp)
      show vStringAt (a :: b :: (w' ++ [x])) c = vStringAt (a :: b :: w') c ++
        [(letterZTile x, lastPosOf (vStringAt (a :: b :: w') c) + vOffset x)]
      rw [vStr_cons2 a b (w' ++ [x]) c, e2, vStr_cons2 a b w' c,
        lastPos_cons_of_ne _ _ hne]
      simp

/-- Reflection of a single tile: a point of the tile of letter `x` reflects through `shR x` to the same tile type. -/
theorem refl_letter (x : Letter) (s : GInt) (hs : s ∈ tileShape (letterZTile x)) :
    shR x - s ∈ tileShape (letterZTile x) := by
  cases x
  · exact refl_p s hs
  · exact refl_q s hs

/-- **The reflected covering of a forward vertical string.** -/
theorem vert_cover_reflect : ∀ (h : BinaryWord) (e : Letter) (c0 c z : GInt), h.getLast? = some e →
    tileCovers (vStringAt h c0) z →
      tileCovers (vRevStringAt h.reverse c) (c + lastPosOf (vStringAt h c0) + shR e - z) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro e c0 c z he; simp at he
  | append_singleton L x ih =>
    intro e c0 c z he hz
    have hx : x = e := by simpa using he
    subst hx
    rcases List.eq_nil_or_concat L with rfl | ⟨M, y, rfl⟩
    · -- the single letter `x`
      simp only [List.nil_append] at hz ⊢
      rw [vStr_single, tileCovers_cons'] at hz
      simp only [tileCovers_nil', or_false] at hz
      obtain ⟨s, hs, hsz⟩ := List.mem_map.1 hz
      have hsz' : s + c0 = z := hsz
      have hl : lastPosOf (vStringAt [x] c0) = c0 := by
        rw [vStr_single]; simp [lastPosOf]
      rw [hl, List.reverse_singleton, vRev_single, tileCovers_cons']
      simp only [tileCovers_nil', or_false]
      refine List.mem_map.2 ⟨shR x - s, refl_letter x s hs, ?_⟩
      rw [← hsz']
      abel
    · -- the step: the letter `x` after the word `M ++ [y]`
      simp only [List.concat_eq_append] at hz ih ⊢
      have hne : M ++ [y] ≠ [] := by simp
      rw [vStr_append (M ++ [y]) c0 x hne] at hz
      rw [tileCovers_append_single'] at hz
      have hrev : ((M ++ [y]) ++ [x]).reverse = x :: y :: M.reverse := by simp
      rw [vStr_append (M ++ [y]) c0 x hne, lastPos_append_single, hrev, vRev_cons2]
      rcases hz with hz1 | hz2
      · -- covered by the forward word `M ++ [y]`: the induction hypothesis, reflected through the shifted centre
        have hy : (M ++ [y]).getLast? = some y := by simp
        have hih := ih y c0 (c + vRevOffset x y) z hy hz1
        have hrv : (M ++ [y]).reverse = y :: M.reverse := by simp
        rw [hrv] at hih
        have hpt : c + (lastPosOf (vStringAt (M ++ [y]) c0) + vOffset x) + shR x - z =
            c + vRevOffset x y + lastPosOf (vStringAt (M ++ [y]) c0) + shR y - z := by
          rw [vrev_offset_identity]
          abel
        rw [tileCovers_cons']
        right
        rw [hpt]
        exact hih
      · -- covered by the new tile of letter `x`: the first reversed tile covers the reflected point
        rw [tileCovers_cons']
        left
        obtain ⟨s, hs, hsz⟩ := List.mem_map.1 hz2
        have hsz' : s + (lastPosOf (vStringAt (M ++ [y]) c0) + vOffset x) = z := hsz
        refine List.mem_map.2 ⟨shR x - s, refl_letter x s hs, ?_⟩
        rw [← hsz']
        ext <;> simp <;> omega

/-! ### The last position of a forward vertical string, and the centre identity -/

theorem vertWord_cons_p (w : Word) : ∃ t, vertWord w = Letter.p :: t := by
  have hh := (StringCorners.vertWord_head_last w).1
  rcases h : vertWord w with _ | ⟨x, t⟩
  · rw [h] at hh; simp at hh
  · rw [h] at hh
    have hx : x = Letter.p := by simpa using hh
    exact ⟨t, by rw [hx]⟩

theorem cnt_pp (t : BinaryWord) : (Letter.p :: t).count Letter.p = t.count Letter.p + 1 := by
  rw [List.count_cons_self]
theorem cnt_qq (t : BinaryWord) : (Letter.q :: t).count Letter.q = t.count Letter.q + 1 := by
  rw [List.count_cons_self]
theorem cnt_qp (t : BinaryWord) : (Letter.q :: t).count Letter.p = t.count Letter.p := by
  rw [List.count_cons_of_ne (by decide)]
theorem cnt_pq (t : BinaryWord) : (Letter.p :: t).count Letter.q = t.count Letter.q := by
  rw [List.count_cons_of_ne (by decide)]

theorem vStr_lastPos : ∀ (h : BinaryWord) (c : GInt), h ≠ [] →
    lastPosOf (vStringAt h c) =
      c + ((-((h.tail.count Letter.p : ℕ) : ℤ)), ((h.length : ℤ) - 1 + ((h.tail.count Letter.q : ℕ) : ℤ)))
  | [], _, h => absurd rfl h
  | [a], c, _ => by simp [vStr_single, lastPosOf]
  | a :: b :: t, c, _ => by
    obtain ⟨rest, hr⟩ := vStr_head b t (c + vOffset b)
    have hne : vStringAt (b :: t) (c + vOffset b) ≠ [] := by
      rw [hr]; exact List.cons_ne_nil _ _
    have ih := vStr_lastPos (b :: t) (c + vOffset b) (List.cons_ne_nil _ _)
    rw [vStr_cons2, lastPos_cons_of_ne _ _ hne, ih]
    cases b <;> simp only [cnt_pp, cnt_qq, cnt_qp, cnt_pq, List.tail_cons, List.length_cons, vOffset] <;>
      ext <;> simp <;> omega

/-- The centre identity of the odd tile: the last position of the vertical string, plus the reflection shift of its last
letter `q`, is the sum of the bottom edge and the right edge of the odd tile. -/
theorem centre_odd (w : Word) :
    lastPosOf (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) + shR Letter.q =
      F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) := by
  obtain ⟨t, ht⟩ := vertWord_cons_p w
  have hv : vWordOf w false = Letter.p :: t := ht
  have hcp : ((vertWord w).count Letter.p : ℤ) = (fracOdd w).den - (fracOdd w).num := (vertWord_counts w).1
  have hcq : ((vertWord w).count Letter.q : ℤ) = (fracOdd w).num := (vertWord_counts w).2
  have hlen : ((vertWord w).length : ℤ) =
      ((vertWord w).count Letter.p : ℤ) + ((vertWord w).count Letter.q : ℤ) := by
    have := length_eq_counts (vertWord w)
    exact_mod_cast this
  rw [ht] at hcp hcq hlen
  simp only [cnt_pp, cnt_pq, List.length_cons] at hcp hcq hlen
  have hV := vStr_lastPos (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))
    (by rw [hv]; exact List.cons_ne_nil _ _)
  rw [hv] at hV ⊢
  simp only [List.tail_cons] at hV
  have hH : lastPosOf (hStringAt (hWordOf w false) 0) = almostV₁ (oddBottom w) - (1, 1) :=
    CornerPositions.lastPos_hWordOf_false w
  have hsb : F2Word.sum (oddBottom w) + gI = texV1Odd (fracOdd w) := sum_oddBottom w
  have hsr : F2Word.sum (oddRight w) - gOne = texV2 (fracOdd w) := sum_oddRight w
  rw [hV, hH]
  unfold almostV₁
  rw [hsb]
  have key1 := congrArg Prod.fst hsb
  have key2 := congrArg Prod.snd hsb
  have key3 := congrArg Prod.fst hsr
  have key4 := congrArg Prod.snd hsr
  ext <;> simp [shR, gI, gOne, texV1Odd, texV2] at key1 key2 key3 key4 ⊢ <;> omega

/-- **S4, odd tile.** Given S3' (the right walk of the odd tile is covered by the forward vertical string), the left side of
the walk, translated by `texV1Odd`, is covered by the reversed vertical string started at `texV1Odd`. -/
theorem S4_odd (w : Word)
    (S3 : ∀ z ∈ F2Word.walk (F2Word.sum (oddBottom w)) (oddRight w),
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z) :
    ∀ t ∈ (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y),
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) (t + texV1Odd (fracOdd w)) := by
  intro t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
  have hp : F2Word.sum (oddBottom w) + y ∈ F2Word.walk (F2Word.sum (oddBottom w)) (oddRight w) := by
    rw [WalkDecomp.walk_translate]
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  have hcov := S3 _ hp
  have hlast : (vWordOf w false).getLast? = some Letter.q := (StringCorners.vertWord_head_last w).2
  have hR := vert_cover_reflect (vWordOf w false) Letter.q _ (texV1Odd (fracOdd w)) _ hlast hcov
  have hc := centre_odd w
  have hpt : texV1Odd (fracOdd w) +
      lastPosOf (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) + shR Letter.q -
        (F2Word.sum (oddBottom w) + y) =
      F2Word.sum (oddRight w) - y + texV1Odd (fracOdd w) := by
    rw [show texV1Odd (fracOdd w) +
        lastPosOf (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) + shR Letter.q -
          (F2Word.sum (oddBottom w) + y) =
        texV1Odd (fracOdd w) +
          (lastPosOf (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) + shR Letter.q) -
          (F2Word.sum (oddBottom w) + y) by abel, hc]
    abel
  rw [hpt] at hR
  exact hR

/-- The centre identity of the even tile: the same identity for the even vertical string and the even bottom and right edges. -/
theorem centre_even (w : Word) :
    lastPosOf (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) + shR Letter.q =
      F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) := by
  have hh := (StringCorners.vWord_even_head_last w).1
  obtain ⟨t, ht⟩ : ∃ t, vWordOf w true = Letter.p :: t := by
    rcases h : vWordOf w true with _ | ⟨x, t⟩
    · rw [h] at hh; simp at hh
    · rw [h] at hh
      have hx : x = Letter.p := by simpa using hh
      exact ⟨t, by rw [hx]⟩
  have hcp : ((vWordOf w true).count Letter.p : ℤ) = (fracEven w).den - (fracEven w).num :=
    (StringCorners.vWord_even_counts w).1
  have hcq : ((vWordOf w true).count Letter.q : ℤ) = (fracEven w).num :=
    (StringCorners.vWord_even_counts w).2
  have hlen : ((vWordOf w true).length : ℤ) =
      ((vWordOf w true).count Letter.p : ℤ) + ((vWordOf w true).count Letter.q : ℤ) := by
    have := length_eq_counts (vWordOf w true)
    exact_mod_cast this
  rw [ht] at hcp hcq hlen
  simp only [cnt_pp, cnt_pq, List.length_cons] at hcp hcq hlen
  have hV := vStr_lastPos (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))
    (by rw [ht]; exact List.cons_ne_nil _ _)
  rw [ht] at hV ⊢
  simp only [List.tail_cons] at hV
  have hH : lastPosOf (hStringAt (hWordOf w true) 0) = almostV₁ (evenBottom w) - (1, 1) :=
    CornerPositions.lastPos_hWordOf_true w
  have hsb : F2Word.sum (evenBottom w) + gI = texV1Even (fracEven w) := sum_evenBottom w
  have hsr : F2Word.sum (evenRight w) - gOne = texV2 (fracEven w) := sum_evenRight w
  rw [hV, hH]
  unfold almostV₁
  rw [hsb]
  have key1 := congrArg Prod.fst hsb
  have key2 := congrArg Prod.snd hsb
  have key3 := congrArg Prod.fst hsr
  have key4 := congrArg Prod.snd hsr
  ext <;> simp [shR, gI, gOne, texV1Even, texV2] at key1 key2 key3 key4 ⊢ <;> omega

/-- **S4, even tile.** The even analogue of `S4_odd`. -/
theorem S4_even (w : Word)
    (S3 : ∀ z ∈ F2Word.walk (F2Word.sum (evenBottom w)) (evenRight w),
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z) :
    ∀ t ∈ (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y),
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) (t + texV1Even (fracEven w)) := by
  intro t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
  have hp : F2Word.sum (evenBottom w) + y ∈ F2Word.walk (F2Word.sum (evenBottom w)) (evenRight w) := by
    rw [WalkDecomp.walk_translate]
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  have hcov := S3 _ hp
  have hlast : (vWordOf w true).getLast? = some Letter.q := (StringCorners.vWord_even_head_last w).2
  have hR := vert_cover_reflect (vWordOf w true) Letter.q _ (texV1Even (fracEven w)) _ hlast hcov
  have hc := centre_even w
  have hpt : texV1Even (fracEven w) +
      lastPosOf (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) + shR Letter.q -
        (F2Word.sum (evenBottom w) + y) =
      F2Word.sum (evenRight w) - y + texV1Even (fracEven w) := by
    rw [show texV1Even (fracEven w) +
        lastPosOf (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) + shR Letter.q -
          (F2Word.sum (evenBottom w) + y) =
        texV1Even (fracEven w) +
          (lastPosOf (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) + shR Letter.q) -
          (F2Word.sum (evenBottom w) + y) by abel, hc]
    abel
  rw [hpt] at hR
  exact hR

end FLatticePaper.Tiles.VerticalReflect
