import FLatticePaper.Tiles.GlueRespectsAll
import FLatticePaper.Tiles.ClosedPathExcluded
import FLatticePaper.Tiles.ClosedPathDiagonal

/-! # Bounds of the blocks of a child string

Every step of the four boundary strings of a standard tile is monotone in each of the coordinates `x`, `y`, `x + y`, `x - y`
(the steps are `2, 1 + i` for the bottom string, `2 + i, 2, 1, 1 + i` for the top one, `-1 + i, 2i` for the right one and
`-1 + 2i, -1 + i, i, 2i` for the left one; `hOffset`, `hRevOffset`, `vOffset`, `vRevOffset`). So the sites of a string lie
between its first and its last position in each of these coordinates, up to the extent of the tiles (`bot_lin`, `top_lin`,
`right_lin`, `left_lin`). With the last digit of the word, the parents are linear in the previous parents (`last_facts`), which
gives the linear facts on the fractions used to separate the blocks of a copy from the earlier copies of its register. -/

namespace FLatticePaper.Tiles.GlueBlockBounds

open FLatticePaper.Farey FLatticePaper.Tiles

/-! ### Monotone strings -/

theorem lin_add (a b : ℤ) (x y : GInt) : a * (x + y).1 + b * (x + y).2 = (a * x.1 + b * x.2) + (a * y.1 + b * y.2) := by
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem sum_lin (a b : ℤ) : ∀ (L : List GInt), (∀ v ∈ L, 0 ≤ a * v.1 + b * v.2) → 0 ≤ a * L.sum.1 + b * L.sum.2
  | [], _ => by simp
  | v :: L, hL => by
    have h1 := hL v List.mem_cons_self
    have h2 := sum_lin a b L (fun u hu => hL u (List.mem_cons_of_mem v hu))
    rw [List.sum_cons, lin_add]
    linarith

/-- The positions of a string with steps of nonnegative `a x + b y` lie between the first and the last one. -/
theorem scanl_lin (a b : ℤ) : ∀ (L : List GInt) (c : GInt), (∀ v ∈ L, 0 ≤ a * v.1 + b * v.2) →
    ∀ e ∈ List.scanl (· + ·) c L, a * c.1 + b * c.2 ≤ a * e.1 + b * e.2 ∧
      a * e.1 + b * e.2 ≤ a * c.1 + b * c.2 + (a * L.sum.1 + b * L.sum.2)
  | [], c, _, e, he => by
    simp only [List.scanl_nil, List.mem_singleton] at he
    subst he
    simp
  | v :: L, c, hL, e, he => by
    have hv := hL v List.mem_cons_self
    have hL' : ∀ u ∈ L, 0 ≤ a * u.1 + b * u.2 := fun u hu => hL u (List.mem_cons_of_mem v hu)
    have hs := sum_lin a b L hL'
    rw [List.sum_cons, lin_add]
    simp only [List.scanl_cons, List.mem_cons] at he
    rcases he with rfl | he
    · constructor <;> linarith
    · have ih := scanl_lin a b L (c + v) hL' e he
      rw [lin_add] at ih
      constructor <;> linarith [ih.1, ih.2]

/-- **The sites of a monotone string** lie between its first and its last position, up to the extent of its tiles. -/
theorem str_lin (ts : List ZTile) (c : GInt) (L : List GInt) (hl : ts.length = L.length + 1) (a b lo hi : ℤ)
    (hL : ∀ v ∈ L, 0 ≤ a * v.1 + b * v.2) (ht : ∀ t ∈ ts, ∀ y ∈ tileShape t, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi)
    (z : GInt) (hz : z ∈ placedSites (ts.zip (List.scanl (· + ·) c L))) :
    a * c.1 + b * c.2 + lo ≤ a * z.1 + b * z.2 ∧
      a * z.1 + b * z.2 ≤ a * (lastPosOf (ts.zip (List.scanl (· + ·) c L))).1 +
        b * (lastPosOf (ts.zip (List.scanl (· + ·) c L))).2 + hi := by
  rw [ClosedPathCorners.lastPos_zip_scanl L ts c hl, lin_add]
  unfold placedSites at hz
  obtain ⟨⟨ty, pos⟩, htp, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  have hm := List.of_mem_zip htp
  have hp := scanl_lin a b L c hL pos hm.2
  have hy' := ht ty hm.1 y hy
  rw [lin_add]
  constructor <;> linarith [hp.1, hp.2, hy'.1, hy'.2]

theorem tile_lin (a b lo hi : ℤ) (h0 : ∀ y ∈ tileShape ZTile.zero, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi)
    (h1 : ∀ y ∈ tileShape ZTile.one, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi)
    (h2 : ∀ y ∈ tileShape ZTile.oneD, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi) (ts : List ZTile) :
    ∀ t ∈ ts, ∀ y ∈ tileShape t, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi := by
  intro t _
  cases t
  exacts [h0, h1, h2]

theorem vtile_lin (a b lo hi : ℤ) (h0 : ∀ y ∈ tileShape ZTile.zero, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi)
    (h1 : ∀ y ∈ tileShape ZTile.one, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi) (w : BinaryWord) :
    ∀ t ∈ w.map letterZTile, ∀ y ∈ tileShape t, lo ≤ a * y.1 + b * y.2 ∧ a * y.1 + b * y.2 ≤ hi := by
  intro t ht
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht
  cases l
  exacts [h0, h1]

theorem len_h (w : BinaryWord) (hw : w ≠ []) : (tileSeq w).length = (w.tail.map hOffset).length + 1 := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [tileSeq, StringJoin.tileSeqAux_length]

theorem len_hr (w : BinaryWord) (hw : w ≠ []) :
    (tileSeq w).length = ((w.zip w.tail).map fun ab => hRevOffset ab.1 ab.2).length + 1 := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [tileSeq, StringJoin.tileSeqAux_length]

theorem len_v (w : BinaryWord) (hw : w ≠ []) : (w.map letterZTile).length = (w.tail.map vOffset).length + 1 := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  simp

theorem len_vr (w : BinaryWord) (hw : w ≠ []) :
    (w.map letterZTile).length = ((w.zip w.tail).map fun ab => vRevOffset ab.1 ab.2).length + 1 := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_ne_nil hw
  simp

/-- **The bounds of a bottom string**, with `e` its last position. -/
theorem bot_lin (w : BinaryWord) (c : GInt) (hw : w ≠ []) (z : GInt) (hz : z ∈ placedSites (hStringAt w c)) :
    c.1 - 1 ≤ z.1 ∧ z.1 ≤ (lastPosOf (hStringAt w c)).1 + 1 ∧ c.2 - 1 ≤ z.2 ∧ z.2 ≤ (lastPosOf (hStringAt w c)).2 + 2 ∧ c.1 + c.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ (lastPosOf (hStringAt w c)).1 + (lastPosOf (hStringAt w c)).2 + 3 ∧
      c.1 - c.2 - 2 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ (lastPosOf (hStringAt w c)).1 - (lastPosOf (hStringAt w c)).2 + 2 := by
  have hs : ∀ (a b : ℤ), (∀ l : Letter, 0 ≤ a * (hOffset l).1 + b * (hOffset l).2) →
      ∀ v ∈ w.tail.map hOffset, 0 ≤ a * v.1 + b * v.2 := by
    intro a b h v hv
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hv
    exact h l
  have k := fun a b lo hi hL h0 h1 h2 =>
    str_lin (tileSeq w) c (w.tail.map hOffset) (len_h w hw) a b lo hi (hs a b hL) (tile_lin a b lo hi h0 h1 h2 _) z hz
  have k1 := k 1 0 (-1) 1 (by intro l; cases l <;> decide) (by decide) (by decide) (by decide)
  have k2 := k 0 1 (-1) 2 (by intro l; cases l <;> decide) (by decide) (by decide) (by decide)
  have k3 := k 1 1 0 3 (by intro l; cases l <;> decide) (by decide) (by decide) (by decide)
  have k4 := k 1 (-1) (-2) 2 (by intro l; cases l <;> decide) (by decide) (by decide) (by decide)
  unfold hStringAt
  omega

/-- **The bounds of a top string.** -/
theorem top_lin (w : BinaryWord) (c : GInt) (hw : w ≠ []) (z : GInt) (hz : z ∈ placedSites (hRevStringAt w c)) :
    c.1 - 1 ≤ z.1 ∧ z.1 ≤ (lastPosOf (hRevStringAt w c)).1 + 1 ∧ c.2 - 1 ≤ z.2 ∧ z.2 ≤ (lastPosOf (hRevStringAt w c)).2 + 2 ∧ c.1 + c.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ (lastPosOf (hRevStringAt w c)).1 + (lastPosOf (hRevStringAt w c)).2 + 3 ∧
      c.1 - c.2 - 2 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ (lastPosOf (hRevStringAt w c)).1 - (lastPosOf (hRevStringAt w c)).2 + 2 := by
  have hs : ∀ (a b : ℤ), (∀ l m : Letter, 0 ≤ a * (hRevOffset l m).1 + b * (hRevOffset l m).2) →
      ∀ v ∈ (w.zip w.tail).map (fun ab => hRevOffset ab.1 ab.2), 0 ≤ a * v.1 + b * v.2 := by
    intro a b h v hv
    obtain ⟨⟨l, m⟩, -, rfl⟩ := List.mem_map.1 hv
    exact h l m
  have k := fun a b lo hi hL h0 h1 h2 =>
    str_lin (tileSeq w) c _ (len_hr w hw) a b lo hi (hs a b hL) (tile_lin a b lo hi h0 h1 h2 _) z hz
  have k1 := k 1 0 (-1) 1 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide) (by decide)
  have k2 := k 0 1 (-1) 2 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide) (by decide)
  have k3 := k 1 1 0 3 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide) (by decide)
  have k4 := k 1 (-1) (-2) 2 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide) (by decide)
  unfold hRevStringAt
  omega

/-- **The bounds of a right string** (`x` and `x - y` decrease along it). -/
theorem right_lin (w : BinaryWord) (c : GInt) (hw : w ≠ []) (z : GInt) (hz : z ∈ placedSites (vStringAt w c)) :
    (lastPosOf (vStringAt w c)).1 ≤ z.1 ∧ z.1 ≤ c.1 + 1 ∧ c.2 ≤ z.2 ∧ z.2 ≤ (lastPosOf (vStringAt w c)).2 + 2 ∧ c.1 + c.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ (lastPosOf (vStringAt w c)).1 + (lastPosOf (vStringAt w c)).2 + 3 ∧
      (lastPosOf (vStringAt w c)).1 - (lastPosOf (vStringAt w c)).2 - 2 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ c.1 - c.2 + 1 := by
  have hs : ∀ (a b : ℤ), (∀ l : Letter, 0 ≤ a * (vOffset l).1 + b * (vOffset l).2) →
      ∀ v ∈ w.tail.map vOffset, 0 ≤ a * v.1 + b * v.2 := by
    intro a b h v hv
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hv
    exact h l
  have k := fun a b lo hi hL h0 h1 =>
    str_lin (w.map letterZTile) c (w.tail.map vOffset) (len_v w hw) a b lo hi (hs a b hL) (vtile_lin a b lo hi h0 h1 w) z hz
  have k1 := k (-1) 0 (-1) 0 (by intro l; cases l <;> decide) (by decide) (by decide)
  have k2 := k 0 1 0 2 (by intro l; cases l <;> decide) (by decide) (by decide)
  have k3 := k 1 1 0 3 (by intro l; cases l <;> decide) (by decide) (by decide)
  have k4 := k (-1) 1 (-1) 2 (by intro l; cases l <;> decide) (by decide) (by decide)
  unfold vStringAt
  omega

/-- **The bounds of a left string** (`x` and `x - y` decrease along it). -/
theorem left_lin (w : BinaryWord) (c : GInt) (hw : w ≠ []) (z : GInt) (hz : z ∈ placedSites (vRevStringAt w c)) :
    (lastPosOf (vRevStringAt w c)).1 ≤ z.1 ∧ z.1 ≤ c.1 + 1 ∧ c.2 ≤ z.2 ∧ z.2 ≤ (lastPosOf (vRevStringAt w c)).2 + 2 ∧ c.1 + c.2 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ (lastPosOf (vRevStringAt w c)).1 + (lastPosOf (vRevStringAt w c)).2 + 3 ∧
      (lastPosOf (vRevStringAt w c)).1 - (lastPosOf (vRevStringAt w c)).2 - 2 ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ c.1 - c.2 + 1 := by
  have hs : ∀ (a b : ℤ), (∀ l m : Letter, 0 ≤ a * (vRevOffset l m).1 + b * (vRevOffset l m).2) →
      ∀ v ∈ (w.zip w.tail).map (fun ab => vRevOffset ab.1 ab.2), 0 ≤ a * v.1 + b * v.2 := by
    intro a b h v hv
    obtain ⟨⟨l, m⟩, -, rfl⟩ := List.mem_map.1 hv
    exact h l m
  have k := fun a b lo hi hL h0 h1 =>
    str_lin (w.map letterZTile) c _ (len_vr w hw) a b lo hi (hs a b hL) (vtile_lin a b lo hi h0 h1 w) z hz
  have k1 := k (-1) 0 (-1) 0 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide)
  have k2 := k 0 1 0 2 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide)
  have k3 := k 1 1 0 3 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide)
  have k4 := k (-1) 1 (-1) 2 (by intro l m; cases l <;> cases m <;> decide) (by decide) (by decide)
  unfold vRevStringAt
  omega

/-! ### The parents after the last digit -/

/-- **The parents are linear in the previous parents**, by the last digit of the word, and the previous parents satisfy the
bounds and parities of a frame; their denominators sum to at least `3` unless the word has one letter. -/
theorem last_facts (w : Word) (hw : w ≠ []) :
    ∃ p' q' : Fraction, 1 ≤ p'.den - p'.num ∧ 0 ≤ p'.num ∧ 1 ≤ q'.num ∧ 0 ≤ q'.den - q'.num ∧
      (p'.num + p'.den) % 2 = 1 ∧ (q'.num + q'.den) % 2 = 0 ∧ ((∃ d, w = [d]) ∨ 3 ≤ p'.den + q'.den) ∧
      (w.getLast? = some Digit.one → (parentsAt w).odd.num = p'.num + q'.num ∧ (parentsAt w).odd.den = p'.den + q'.den ∧
        (parentsAt w).even.num = 2 * p'.num + q'.num ∧ (parentsAt w).even.den = 2 * p'.den + q'.den) ∧
      (w.getLast? = some Digit.two → (parentsAt w).odd.num = p'.num + q'.num ∧ (parentsAt w).odd.den = p'.den + q'.den ∧
        (parentsAt w).even.num = q'.num ∧ (parentsAt w).even.den = q'.den) ∧
      (w.getLast? = some Digit.three → (parentsAt w).odd.num = p'.num ∧ (parentsAt w).odd.den = p'.den ∧
        (parentsAt w).even.num = 2 * p'.num + q'.num ∧ (parentsAt w).even.den = 2 * p'.den + q'.den) := by
  rcases List.eq_nil_or_concat w with h | ⟨v, d, rfl⟩
  · exact absurd h hw
  simp only [List.concat_eq_append] at *
  have hb := SiteScope.parents_bounds v
  have hv := parentsAt_valid v
  have ho : ((parentsAt v).odd.num + (parentsAt v).odd.den) % 2 = 1 := hv.odd_parity
  have he : ((parentsAt v).even.num + (parentsAt v).even.den) % 2 = 0 := hv.even_parity
  refine ⟨(parentsAt v).odd, (parentsAt v).even, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, ho, he, ?_, ?_, ?_, ?_⟩
  · rcases List.eq_nil_or_concat v with h | ⟨v', d', rfl⟩
    · exact Or.inl ⟨d, by simp [h]⟩
    · right
      rw [List.concat_eq_append]
      have hb' := SiteScope.parents_bounds v'
      rw [parentsAt_append_singleton]
      cases d' <;> simp only [Parents.step, Parents.current, Parents.combine] <;> omega
  all_goals
    intro hl
    simp at hl
    subst hl
    rw [parentsAt_append_singleton]
    simp only [Parents.step, Parents.current, Parents.combine, and_true, true_and]
    omega

end FLatticePaper.Tiles.GlueBlockBounds
