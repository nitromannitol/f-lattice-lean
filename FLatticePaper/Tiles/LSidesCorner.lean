import FLatticePaper.Tiles.LSidesOddH

/-! # The corners of the sides of a standard child

Each horizontal side string of a standard child and each vertical side string share a site, at their common corner: `0` at the
bottom left, the end `P` of the bottom string at the bottom right (the first tile of the right string), and the half-turn images
`C`, `C - P` at the top right and the top left (`C = v_1 + v_2 + 1 - i`, `top_iff_bottom_odd`, `left_iff_right`). So an odometer
that agrees with the tile odometer of the child up to a constant on two adjacent sides agrees with it up to one constant on both:
the two sides of the elongated L-corrections (`lemma:l_correc_properties` (2)) give `LSidesAgree` from one side each
(`lsides_merge`). -/

namespace FLatticePaper.Tiles.LSidesCorner

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- The first tile of a nonempty tile list lies in its placed sites. -/
theorem head_mem (ts : List (ZTile × GInt)) (hne : ts ≠ []) (t : ZTile) (c : GInt) (h : ts.headD (ZTile.zero, 0) = (t, c))
    (x : GInt) (hx : x ∈ tileShape t) : x + c ∈ placedSites ts := by
  cases ts with
  | nil => exact absurd rfl hne
  | cons a l =>
    simp only [List.headD_cons] at h
    subst h
    simp only [placedSites, List.flatMap_cons, List.mem_append, List.mem_map]
    exact Or.inl ⟨x, hx, rfl⟩

/-- The four corner sites of the side strings of a standard child with words `wh`, `wv` (`wh = q ⋯ p`, `wv = p ⋯ q`). -/
theorem corners (wh wv : BinaryWord) (hh : wh.head? = some Letter.q) (hl : wh.getLast? = some Letter.p)
    (vh : wv.head? = some Letter.p) (vl : wv.getLast? = some Letter.q) :
    ((0 : GInt) ∈ placedSites (sideString wh wv 0 .hPlus) ∧ (0 : GInt) ∈ placedSites (sideString wh wv 0 .vMinus)) ∧
      (lastPosOf (hStringAt wh 0) ∈ placedSites (sideString wh wv 0 .hPlus) ∧
        lastPosOf (hStringAt wh 0) ∈ placedSites (sideString wh wv 0 .vPlus)) := by
  have hwne : wh ≠ [] := fun h => by simp [h] at hh
  have hvne : wv ≠ [] := fun h => by simp [h] at vh
  have z1 : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.one := by decide
  have z0 : ((0 : ℤ), (0 : ℤ)) ∈ tileShape ZTile.zero := by decide
  have e0 : ((0 : ℤ), (0 : ℤ)) + (0 : GInt) = 0 := by ext <;> simp
  have eP : ∀ P : GInt, ((0 : ℤ), (0 : ℤ)) + P = P := fun P => by ext <;> simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [sideString]
    have := head_mem _ (GlueStringDecomp.hStringAt_ne wh 0 hwne) _ _ (hStringAt_head_q wh 0 hh) _ z1
    rw [e0] at this; exact this
  · simp only [sideString]
    have hr : wv.reverse.head? = some Letter.q := by rw [List.head?_reverse]; exact vl
    have := head_mem _ (GlueStringDecomp.vRevStringAt_ne _ 0 (by simpa using hvne)) _ _
      (vRevStringAt_headD_q wv.reverse 0 hr) _ z1
    rw [e0] at this; exact this
  · simp only [sideString]
    have := LSidesOddH.last_mem wh hwne hl _ z0
    rw [eP] at this; exact this
  · simp only [sideString]
    have := head_mem _ (GlueStringDecomp.vStringAt_ne wv (lastPosOf (hStringAt wh 0)) hvne) _ _
      (vStringAt_headD_p wv (lastPosOf (hStringAt wh 0)) vh) _ z0
    rw [eP] at this; exact this

/-- **The four corners of the odd child**: each horizontal side meets each vertical side. -/
theorem corner_odd (w : Word) (sh sv : Side) (hsh : sh = .hPlus ∨ sh = .hMinus) (hsv : sv = .vPlus ∨ sv = .vMinus) :
    ∃ x, x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 sh) ∧
      x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 sv) := by
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := corners (hWordOf w false) (vWordOf w false) (hWordOf_head_last w false).1
    (hWordOf_head_last w false).2 (GlueStringDecomp.vp_head w) (GlueStringDecomp.vp_last w)
  set C := TileHalfTurnStd.cOdd ((parentsAt w).current .odd)
  rcases hsh with rfl | rfl <;> rcases hsv with rfl | rfl
  · exact ⟨_, b1, b2⟩
  · exact ⟨_, a1, a2⟩
  · refine ⟨C - 0, ?_, ?_⟩
    · rw [LSidesOddH.top_iff_bottom_odd, sub_sub_cancel]; exact a1
    · have := (LSidesOddV.left_iff_right w 0).1 a2; exact this
  · refine ⟨C - lastPosOf (hStringAt (hWordOf w false) 0), ?_, ?_⟩
    · rw [LSidesOddH.top_iff_bottom_odd, sub_sub_cancel]; exact b1
    · rw [LSidesOddV.left_iff_right, sub_sub_cancel]; exact b2

/-- **The left side of the even child is the half-turn of its right side** about the centre `v_1 + v_2 + 1 - i`. -/
theorem left_iff_right_even (w : Word) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .vMinus) ↔
      TileHalfTurnStd.cEven ((parentsAt w).current .even) - x ∈
        placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .vPlus) := by
  simp only [sideString]
  rw [ReflectedCoverConverse.placed_vRev_iff (vWordOf w true) Letter.q (GlueStringDecomp.vq_last w)
    (lastPosOf (hStringAt (hWordOf w true) 0)) 0 x]
  have e : lastPosOf (hStringAt (hWordOf w true) 0) + lastPosOf (vStringAt (vWordOf w true) (0, 0)) +
      ReflectedCover.shR Letter.q + 0 = TileHalfTurnStd.cEven ((parentsAt w).current .even) := by
    have h1 := GlueStringDecomp.lp_bot_even w 0
    have h2 := GlueStringDecomp.lp_right_even w (0, 0)
    rw [h1, h2]
    simp only [TileHalfTurnStd.cEven, ReflectedCover.shR, fracEven]
    ext <;> (simp; try ring)
  rw [e]

/-- **The four corners of the even child**: each horizontal side meets each vertical side. -/
theorem corner_even (w : Word) (sh sv : Side) (hsh : sh = .hPlus ∨ sh = .hMinus) (hsv : sv = .vPlus ∨ sv = .vMinus) :
    ∃ x, x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 sh) ∧
      x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 sv) := by
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := corners (hWordOf w true) (vWordOf w true) (hWordOf_head_last w true).1
    (hWordOf_head_last w true).2 (GlueStringDecomp.vq_head w) (GlueStringDecomp.vq_last w)
  set C := TileHalfTurnStd.cEven ((parentsAt w).current .even)
  have tb : ∀ x, x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hMinus) ↔
      C - x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus) := by
    intro x
    rw [LSidesEvenK.top_iff_bottom w x]
  rcases hsh with rfl | rfl <;> rcases hsv with rfl | rfl
  · exact ⟨_, b1, b2⟩
  · exact ⟨_, a1, a2⟩
  · refine ⟨C - 0, ?_, ?_⟩
    · rw [tb, sub_sub_cancel]; exact a1
    · exact (left_iff_right_even w 0).1 a2
  · refine ⟨C - lastPosOf (hStringAt (hWordOf w true) 0), ?_, ?_⟩
    · rw [tb, sub_sub_cancel]; exact b1
    · rw [left_iff_right_even, sub_sub_cancel]; exact b2

/-- **Two sides that meet**: agreement up to a constant on each of two sides with a common site, and the respect of each side,
give `LSidesAgree` for the two sides. -/
theorem lsides_merge (L T : PartialOdometer) (wh wv : BinaryWord) (s1 s2 : Side)
    (hx : ∃ x, x ∈ placedSites (sideString wh wv 0 s1) ∧ x ∈ placedSites (sideString wh wv 0 s2))
    (h1 : RespectsTiles (sideOrient s1).1 (sideOrient s1).2 (sideString wh wv 0 s1) L.val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString wh wv 0 s1), x ∈ L.dom ∧ x ∈ T.dom ∧ L.val x = T.val x + c)
    (h2 : RespectsTiles (sideOrient s2).1 (sideOrient s2).2 (sideString wh wv 0 s2) L.val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString wh wv 0 s2), x ∈ L.dom ∧ x ∈ T.dom ∧ L.val x = T.val x + c) :
    LSidesAgree L T wh wv [s1, s2] := by
  obtain ⟨x, hx1, hx2⟩ := hx
  obtain ⟨r1, c1, hc1⟩ := h1
  obtain ⟨r2, c2, hc2⟩ := h2
  have e : c1 = c2 := by
    have := (hc1 x hx1).2.2
    have := (hc2 x hx2).2.2
    linarith
  refine ⟨fun s hs => ?_, c1, fun s hs y hy => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact r1
    · exact r2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hc1 y hy
    · rw [e]; exact hc2 y hy

/-- One side: the respect and the agreement on it give `LSidesAgree` for that side. -/
theorem lsides_single (L T : PartialOdometer) (wh wv : BinaryWord) (s1 : Side)
    (h1 : RespectsTiles (sideOrient s1).1 (sideOrient s1).2 (sideString wh wv 0 s1) L.val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString wh wv 0 s1), x ∈ L.dom ∧ x ∈ T.dom ∧ L.val x = T.val x + c) :
    LSidesAgree L T wh wv [s1] := by
  obtain ⟨r1, c1, hc1⟩ := h1
  refine ⟨fun s hs => ?_, c1, fun s hs y hy => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; exact r1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; exact hc1 y hy

end FLatticePaper.Tiles.LSidesCorner
