import FLatticePaper.Tiles.ZeroOneStringPositions
import Mathlib.Data.Int.Interval

/-! Simple connectivity of the stacked zero-one strings (`lemma:zero-one-fixed-offsets`, last sentence).

Reading. A finite set `S` of cells (a cell is its lower-left corner) is simply connected when
* `FourConnected S`: any two cells are joined by a chain of cells of `S`, consecutive ones sharing an edge; and
* `HoleFree S`: for every box strictly enclosing `S`, every cell of the box outside `S` reaches the corner of the box
  through cells of the box outside `S`. This is "the complement inside the bounding box enlarged by one is 4-connected".

Stacked string. For a word `w` the site set of its stacked string is the union of the placed tiles of `B_w` (letters `w`,
offsets `stringPositions o false w`) and of `B^r_{rev w}` (letters `w.reverse`, offsets `stringPositions o true w.reverse`,
translated by `c(T_1^+) - c(T_1^-)`). Horizontal strings use the enlarged one-tile `T^d_{1/1}` after a one-tile
(paper line 1296), vertical strings none (paper line 1348).

Method. Two one-dimensional conditions suffice: `RowConvex S` (every row meets `S` in an interval) gives holes-freeness,
and with `RowsLinked S` (consecutive rows share a column) it gives 4-connectivity. Both are decidable and are checked by
`decide` on every almost palindrome of length at most six. -/

namespace FLatticePaper.Tiles

open Relation

/-! ### The site set of a stacked zero-one string -/

/-- The enlarged one-tile `T^d_{1/1} = T_{1/1} ∪ {i - 1, 1 - i}` (paper line 1296). -/
def oneTileEnlargedSites : List Site := oneTileSites ++ [((-1 : ℤ), (1 : ℤ)), ((1 : ℤ), (-1 : ℤ))]

/-- The sites of a tile: `T_{0/1}` for `p`; for `q` the one-tile, enlarged when its flag is set. -/
def tileSitesOf : Letter → Bool → List Site
  | .p, _ => zeroTileSites
  | .q, false => oneTileSites
  | .q, true => oneTileEnlargedSites

/-- The enlargement flags of a family: the first tile is not enlarged, and a one-tile is enlarged when it follows a
one-tile. Only horizontal strings are enlarged. -/
def enlargedFlags (o : Orientation) (L : BinaryWord) : List Bool :=
  false :: List.zipWith
    (fun a b => decide (o = Orientation.horizontal) && decide (a = Letter.q) && decide (b = Letter.q)) L L.tail

/-- The sites of one family of tiles: the tile of each letter, placed at its offset (`stringPositions`) and translated
by `shift`. -/
def familySites (o : Orientation) (rev : Bool) (L : BinaryWord) (shift : Site) : List Site :=
  (List.zip L (List.zip (enlargedFlags o L) (stringPositions o rev L))).flatMap fun t =>
    (tileSitesOf t.1 t.2.1).map fun c => (c.1 + t.2.2.1 + shift.1, c.2 + t.2.2.2 + shift.2)

/-- The offset of the reversed family, `c(T_1^+) - c(T_1^-)`: `-1 + 2i = v_{p,2} + i` (horizontal) and `-1 - i = -v_{q,1}`
(vertical); the reversed family is translated by its negative. -/
def familyShift : Orientation → Site
  | .horizontal => ((1 : ℤ), (-2 : ℤ))
  | .vertical => ((1 : ℤ), (1 : ℤ))

/-- The site set of the stacked zero-one string of `w`: the tiles of `B_w` and of `B^r_{rev w}`. -/
def stackedSites (o : Orientation) (w : BinaryWord) : Finset Site :=
  (familySites o false w (0, 0) ++ familySites o true w.reverse (familyShift o)).toFinset

/-! ### Simple connectivity of a finite set of cells -/

/-- Two cells share an edge. -/
def Adj4 (u v : Site) : Prop :=
  (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
    (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨ (v.1 = u.1 ∧ v.2 = u.2 - 1)

theorem adj4_symm {u v : Site} (h : Adj4 u v) : Adj4 v u := by
  unfold Adj4 at *
  omega

/-- Row convexity: each row of `S` is an interval of integers. -/
def RowConvex (S : Finset Site) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → ∀ x ∈ Finset.Icc a.1 b.1, (x, a.2) ∈ S

/-- Row linking: for two cells of `S` in rows `a.2 ≤ b.2`, each row `y` in `[a.2, b.2)` shares a column with row `y + 1`. -/
def RowsLinked (S : Finset Site) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a.2 ≤ b.2 → ∀ y ∈ Finset.Ico a.2 b.2,
    ∃ x ∈ S.image Prod.fst, (x, y) ∈ S ∧ (x, y + 1) ∈ S

/-- 4-connectivity: any two cells of `S` are joined by a chain of cells of `S`, consecutive ones sharing an edge. -/
def FourConnected (S : Finset Site) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a b

/-- The cells of the box `[x0,x1] × [y0,y1]` outside `S`. -/
def InBoxFree (S : Finset Site) (x0 x1 y0 y1 : ℤ) (p : Site) : Prop :=
  x0 ≤ p.1 ∧ p.1 ≤ x1 ∧ y0 ≤ p.2 ∧ p.2 ≤ y1 ∧ p ∉ S

/-- No holes: for every box strictly enclosing `S`, every cell of the box outside `S` reaches the corner `(x0, y0)`
through cells of the box outside `S`. -/
def HoleFree (S : Finset Site) : Prop :=
  ∀ x0 x1 y0 y1 : ℤ, (∀ s ∈ S, x0 < s.1 ∧ s.1 < x1 ∧ y0 < s.2 ∧ s.2 < y1) →
    ∀ c : Site, InBoxFree S x0 x1 y0 y1 c →
      ReflTransGen (fun u v => InBoxFree S x0 x1 y0 y1 u ∧ InBoxFree S x0 x1 y0 y1 v ∧ Adj4 u v) c (x0, y0)

/-- Simple connectivity of a finite set of cells: 4-connected and without holes (the reading above). -/
def SimplyConnectedCells (S : Finset Site) : Prop := FourConnected S ∧ HoleFree S

/-! ### Row conditions imply simple connectivity -/

/-- A reflexive-transitive closure of a symmetric relation is symmetric. -/
theorem rtg_symm' {r : Site → Site → Prop} (hr : ∀ u v, r u v → r v u) {a b : Site}
    (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hcd ih => exact ReflTransGen.head (hr _ _ hcd) ih

theorem rowChain_le {S : Finset Site} (hR : RowConvex S) (a : Site) (ha : a ∈ S) (b : Site) (hb : b ∈ S)
    (hab : a.2 = b.2) (hle : a.1 ≤ b.1) :
    ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a b := by
  unfold RowConvex at hR
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at hab hle
  subst hab
  have key : ∀ k : ℕ, a1 + (k : ℤ) ≤ b1 →
      ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) (a1, a2) (a1 + (k : ℤ), a2) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, add_zero]
      exact ReflTransGen.refl
    | succ k ih =>
      intro hk
      have hprev : (a1 + (k : ℤ), a2) ∈ S :=
        hR (a1, a2) ha (b1, a2) hb rfl _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hnew : (a1 + ((k + 1 : ℕ) : ℤ), a2) ∈ S :=
        hR (a1, a2) ha (b1, a2) hb rfl _ (Finset.mem_Icc.mpr ⟨by omega, by push_cast at hk ⊢; omega⟩)
      exact (ih (by push_cast at hk; omega)).tail ⟨hprev, hnew, Or.inl ⟨by push_cast; ring, rfl⟩⟩
  have e := key (b1 - a1).toNat (by omega)
  have e' : a1 + ((b1 - a1).toNat : ℤ) = b1 := by omega
  rw [e'] at e
  exact e

theorem rowChain {S : Finset Site} (hR : RowConvex S) (a : Site) (ha : a ∈ S) (b : Site) (hb : b ∈ S)
    (hab : a.2 = b.2) : ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a b := by
  rcases le_total a.1 b.1 with h | h
  · exact rowChain_le hR a ha b hb hab h
  · exact rtg_symm' (fun u v huv => ⟨huv.2.1, huv.1, adj4_symm huv.2.2⟩) (rowChain_le hR b hb a ha hab.symm h)

theorem rtg_of_rows_le {S : Finset Site} (hR : RowConvex S) (hL : RowsLinked S) (a : Site) (ha : a ∈ S)
    (b : Site) (hb : b ∈ S) (hab : a.2 ≤ b.2) :
    ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a b := by
  unfold RowsLinked at hL
  have P : ∀ k : ℕ, ∀ c ∈ S, c.2 = a.2 + (k : ℤ) → ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a c := by
    intro k
    induction k with
    | zero =>
      intro c hc hc2
      simp only [Nat.cast_zero, add_zero] at hc2
      exact rowChain hR a ha c hc hc2.symm
    | succ k ih =>
      intro c hc hc2
      have hy : a.2 + (k : ℤ) ∈ Finset.Ico a.2 c.2 :=
        Finset.mem_Ico.mpr ⟨by omega, by push_cast at hc2; omega⟩
      obtain ⟨x, -, hx1, hx2⟩ := hL a ha c hc (by push_cast at hc2; omega) _ hy
      have h1 : ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a (x, a.2 + (k : ℤ)) := ih _ hx1 rfl
      have h2 : ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) a (x, a.2 + (k : ℤ) + 1) :=
        h1.tail ⟨hx1, hx2, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      have h3 : ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ Adj4 u v) (x, a.2 + (k : ℤ) + 1) c :=
        rowChain hR _ hx2 c hc (by simp only; push_cast at hc2; omega)
      exact h2.trans h3
  exact P (b.2 - a.2).toNat b hb (by omega)

/-- Row convexity and row linking give 4-connectivity. -/
theorem fourConnected_of_rows {S : Finset Site} (hR : RowConvex S) (hL : RowsLinked S) : FourConnected S := by
  intro a ha b hb
  rcases le_total a.2 b.2 with h | h
  · exact rtg_of_rows_le hR hL a ha b hb h
  · exact rtg_symm' (fun u v huv => ⟨huv.2.1, huv.1, adj4_symm huv.2.2⟩) (rtg_of_rows_le hR hL b hb a ha h)

/-- A straight walk of unit steps `d` from `c` stays in the free cells of the box. -/
theorem walk_free (S : Finset Site) (x0 x1 y0 y1 : ℤ) (d : Site)
    (hd : d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)) (c : Site) (k : ℕ)
    (hfree : ∀ j : ℕ, j ≤ k → InBoxFree S x0 x1 y0 y1 (c.1 + (j : ℤ) * d.1, c.2 + (j : ℤ) * d.2)) :
    ReflTransGen (fun u v => InBoxFree S x0 x1 y0 y1 u ∧ InBoxFree S x0 x1 y0 y1 v ∧ Adj4 u v) c
      (c.1 + (k : ℤ) * d.1, c.2 + (k : ℤ) * d.2) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact ReflTransGen.refl
  | succ k ih =>
    have h := ih (fun j hj => hfree j (by omega))
    refine h.tail ⟨hfree k (by omega), hfree (k + 1) le_rfl, ?_⟩
    rcases hd with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨by push_cast; ring, by push_cast; ring⟩
    · exact Or.inr (Or.inl ⟨by push_cast; ring, by push_cast; ring⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by push_cast; ring, by push_cast; ring⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by push_cast; ring, by push_cast; ring⟩))

/-- Row convexity gives holes-freeness: a free cell sees the box boundary along its row and then along a side. -/
theorem holeFree_of_rows {S : Finset Site} (hR : RowConvex S) : HoleFree S := by
  unfold RowConvex at hR
  intro x0 x1 y0 y1 hS c hc
  obtain ⟨hc1, hc2, hc3, hc4, hcS⟩ := hc
  by_cases hl : ∃ s ∈ S, s.2 = c.2 ∧ s.1 < c.1
  · -- a cell of `S` lies left of `c` in its row, so by row convexity none lies right of `c`
    have hr : ¬ ∃ t ∈ S, t.2 = c.2 ∧ c.1 < t.1 := by
      rintro ⟨t, ht, ht2, ht1⟩
      obtain ⟨s, hs, hs2, hs1⟩ := hl
      have hrow : (c.1, s.2) ∈ S :=
        hR s hs t ht (hs2.trans ht2.symm) c.1 (Finset.mem_Icc.mpr ⟨hs1.le, ht1.le⟩)
      apply hcS
      have e : c = (c.1, s.2) := Prod.ext rfl hs2.symm
      rw [e]
      exact hrow
    -- walk right to the side `x1`, then down the side, then left along the bottom row
    have w1 := walk_free S x0 x1 y0 y1 (1, 0) (Or.inl rfl) c (x1 - c.1).toNat (by
      intro j hj
      unfold InBoxFree
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · intro hin
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact hcS (by simpa using hin)
        · exact hr ⟨_, hin, by dsimp only; ring, by dsimp only; omega⟩)
    have e1 : (c.1 + ((x1 - c.1).toNat : ℤ) * (1, 0).1, c.2 + ((x1 - c.1).toNat : ℤ) * (1, 0).2) = (x1, c.2) :=
      Prod.ext (by dsimp only; omega) (by dsimp only; ring)
    rw [e1] at w1
    have w2 := walk_free S x0 x1 y0 y1 (0, -1) (Or.inr (Or.inr (Or.inr rfl))) (x1, c.2) (c.2 - y0).toNat (by
      intro j hj
      unfold InBoxFree
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · intro hin
        have h := hS _ hin
        dsimp only at h
        omega)
    have e2 : ((x1, c.2).1 + ((c.2 - y0).toNat : ℤ) * (0, -1).1,
        (x1, c.2).2 + ((c.2 - y0).toNat : ℤ) * (0, -1).2) = (x1, y0) :=
      Prod.ext (by dsimp only; ring) (by dsimp only; omega)
    rw [e2] at w2
    have w3 := walk_free S x0 x1 y0 y1 (-1, 0) (Or.inr (Or.inl rfl)) (x1, y0) (x1 - x0).toNat (by
      intro j hj
      unfold InBoxFree
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · intro hin
        have h := hS _ hin
        dsimp only at h
        omega)
    have e3 : ((x1, y0).1 + ((x1 - x0).toNat : ℤ) * (-1, 0).1,
        (x1, y0).2 + ((x1 - x0).toNat : ℤ) * (-1, 0).2) = (x0, y0) :=
      Prod.ext (by dsimp only; omega) (by dsimp only; ring)
    rw [e3] at w3
    exact (w1.trans w2).trans w3
  · -- no cell of `S` lies left of `c` in its row: walk left to the side `x0`, then down
    have w1 := walk_free S x0 x1 y0 y1 (-1, 0) (Or.inr (Or.inl rfl)) c (c.1 - x0).toNat (by
      intro j hj
      unfold InBoxFree
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · intro hin
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact hcS (by simpa using hin)
        · exact hl ⟨_, hin, by dsimp only; ring, by dsimp only; omega⟩)
    have e1 : (c.1 + ((c.1 - x0).toNat : ℤ) * (-1, 0).1, c.2 + ((c.1 - x0).toNat : ℤ) * (-1, 0).2) = (x0, c.2) :=
      Prod.ext (by dsimp only; omega) (by dsimp only; ring)
    rw [e1] at w1
    have w2 := walk_free S x0 x1 y0 y1 (0, -1) (Or.inr (Or.inr (Or.inr rfl))) (x0, c.2) (c.2 - y0).toNat (by
      intro j hj
      unfold InBoxFree
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · intro hin
        have h := hS _ hin
        dsimp only at h
        omega)
    have e2 : ((x0, c.2).1 + ((c.2 - y0).toNat : ℤ) * (0, -1).1,
        (x0, c.2).2 + ((c.2 - y0).toNat : ℤ) * (0, -1).2) = (x0, y0) :=
      Prod.ext (by dsimp only; ring) (by dsimp only; omega)
    rw [e2] at w2
    exact w1.trans w2

/-- Row convexity and row linking give simple connectivity. -/
theorem simplyConnectedCells_of_rows {S : Finset Site} (hR : RowConvex S) (hL : RowsLinked S) :
    SimplyConnectedCells S :=
  ⟨fourConnected_of_rows hR hL, holeFree_of_rows hR⟩

/-! ### Decidable row conditions and the check for short words -/

instance rowConvex_decidable (S : Finset Site) : Decidable (RowConvex S) := by
  unfold RowConvex
  infer_instance

instance rowsLinked_decidable (S : Finset Site) : Decidable (RowsLinked S) := by
  unfold RowsLinked
  infer_instance

/-- All binary words of length `n`. -/
def allWordsLen : ℕ → List BinaryWord
  | 0 => [[]]
  | n + 1 => (allWordsLen n).flatMap fun w => [Letter.p :: w, Letter.q :: w]

/-- All binary words of length at most `n`. -/
def wordsUpTo (n : ℕ) : List BinaryWord := (List.range (n + 1)).flatMap allWordsLen

theorem mem_allWordsLen : ∀ (n : ℕ) (w : BinaryWord), w.length = n → w ∈ allWordsLen n := by
  intro n
  induction n with
  | zero =>
    intro w hw
    cases w with
    | nil => simp [allWordsLen]
    | cons a w => simp at hw
  | succ n ih =>
    intro w hw
    cases w with
    | nil => simp at hw
    | cons a w =>
      refine List.mem_flatMap.mpr ⟨w, ih w (by simpa using hw), ?_⟩
      cases a <;> simp

theorem mem_wordsUpTo {w : BinaryWord} (hw : w.length ≤ 6) : w ∈ wordsUpTo 6 :=
  List.mem_flatMap.mpr ⟨w.length, List.mem_range.mpr (by omega), mem_allWordsLen _ w rfl⟩

/-- The Boolean form of `IsAlmostPalindrome`: length at least two and an interior palindrome. -/
def almostPalB (w : BinaryWord) : Bool :=
  decide (2 ≤ w.length) && ((w.drop 1).dropLast.reverse == (w.drop 1).dropLast)

theorem almostPalB_of {w : BinaryWord} (h : IsAlmostPalindrome w) : almostPalB w = true := by
  obtain ⟨f, l, m, hm, rfl⟩ := h
  simp [almostPalB, hm]

set_option maxHeartbeats 400000 in
/-- The almost palindromes of length at most six with head `q` and last letter `p` (the words the horizontal row check runs on). -/
theorem horizontal_words_filter : ∀ w ∈ wordsUpTo 6, almostPalB w = true → w.head? = some Letter.q →
    w.getLast? = some Letter.p →
      w ∈ [[Letter.q, Letter.p], [Letter.q, Letter.p, Letter.p], [Letter.q, Letter.q, Letter.p], [Letter.q, Letter.p, Letter.p, Letter.p],
        [Letter.q, Letter.q, Letter.q, Letter.p], [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p], [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p], [Letter.q, Letter.q, Letter.p, Letter.q, Letter.p],
        [Letter.q, Letter.q, Letter.q, Letter.q, Letter.p], [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p, Letter.p], [Letter.q, Letter.p, Letter.q, Letter.q, Letter.p, Letter.p], [Letter.q, Letter.q, Letter.p, Letter.p, Letter.q, Letter.p],
        [Letter.q, Letter.q, Letter.q, Letter.q, Letter.q, Letter.p]] := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qpp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qppp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qpppp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qpqpp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.q, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqpqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.p, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.p, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqqqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qppppp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.p, Letter.p, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qpqqpp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.p, Letter.q, Letter.q, Letter.p, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.p, Letter.q, Letter.q, Letter.p, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqppqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.p, Letter.p, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.p, Letter.p, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_horizontal_rows_qqqqqp :
    RowConvex (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.q, Letter.q, Letter.p]) ∧ RowsLinked (stackedSites .horizontal [Letter.q, Letter.q, Letter.q, Letter.q, Letter.q, Letter.p]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Horizontal stacked strings of almost palindromes of length at most six: row convexity and row linking, decided. -/
theorem small_horizontal_rows : ∀ w ∈ wordsUpTo 6, almostPalB w = true → w.head? = some Letter.q →
    w.getLast? = some Letter.p →
      RowConvex (stackedSites .horizontal w) ∧ RowsLinked (stackedSites .horizontal w) := by
  intro w hw hA h1 h2
  have hmem := horizontal_words_filter w hw hA h1 h2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_horizontal_rows_qp
  · exact small_horizontal_rows_qpp
  · exact small_horizontal_rows_qqp
  · exact small_horizontal_rows_qppp
  · exact small_horizontal_rows_qqqp
  · exact small_horizontal_rows_qpppp
  · exact small_horizontal_rows_qpqpp
  · exact small_horizontal_rows_qqpqp
  · exact small_horizontal_rows_qqqqp
  · exact small_horizontal_rows_qppppp
  · exact small_horizontal_rows_qpqqpp
  · exact small_horizontal_rows_qqppqp
  · exact small_horizontal_rows_qqqqqp

set_option maxHeartbeats 400000 in
/-- The almost palindromes of length at most six with head `p` and last letter `q` (the words the vertical row check runs on). -/
theorem vertical_words_filter : ∀ w ∈ wordsUpTo 6, almostPalB w = true → w.head? = some Letter.p →
    w.getLast? = some Letter.q →
      w ∈ [[Letter.p, Letter.q], [Letter.p, Letter.p, Letter.q], [Letter.p, Letter.q, Letter.q], [Letter.p, Letter.p, Letter.p, Letter.q],
        [Letter.p, Letter.q, Letter.q, Letter.q], [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q], [Letter.p, Letter.p, Letter.q, Letter.p, Letter.q], [Letter.p, Letter.q, Letter.p, Letter.q, Letter.q],
        [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q], [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q], [Letter.p, Letter.p, Letter.q, Letter.q, Letter.p, Letter.q], [Letter.p, Letter.q, Letter.p, Letter.p, Letter.q, Letter.q],
        [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q, Letter.q]] := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_ppq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pppq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_ppppq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_ppqpq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.q, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.q, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqpqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.p, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.p, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqqqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pppppq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.p, Letter.p, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_ppqqpq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.p, Letter.q, Letter.q, Letter.p, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.p, Letter.q, Letter.q, Letter.p, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqppqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.p, Letter.p, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.p, Letter.p, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
theorem small_vertical_rows_pqqqqq :
    RowConvex (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q, Letter.q]) ∧ RowsLinked (stackedSites .vertical [Letter.p, Letter.q, Letter.q, Letter.q, Letter.q, Letter.q]) := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- Vertical stacked strings of almost palindromes of length at most six: row convexity and row linking, decided. -/
theorem small_vertical_rows : ∀ w ∈ wordsUpTo 6, almostPalB w = true → w.head? = some Letter.p →
    w.getLast? = some Letter.q →
      RowConvex (stackedSites .vertical w) ∧ RowsLinked (stackedSites .vertical w) := by
  intro w hw hA h1 h2
  have hmem := vertical_words_filter w hw hA h1 h2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact small_vertical_rows_pq
  · exact small_vertical_rows_ppq
  · exact small_vertical_rows_pqq
  · exact small_vertical_rows_pppq
  · exact small_vertical_rows_pqqq
  · exact small_vertical_rows_ppppq
  · exact small_vertical_rows_ppqpq
  · exact small_vertical_rows_pqpqq
  · exact small_vertical_rows_pqqqq
  · exact small_vertical_rows_pppppq
  · exact small_vertical_rows_ppqqpq
  · exact small_vertical_rows_pqppqq
  · exact small_vertical_rows_pqqqqq

/-- The vertical stacked string of an almost palindrome `w = p … q` of length at most six is simply connected. -/
theorem stacked_vertical_simply_connected_short {w : BinaryWord} (hw : w.length ≤ 6)
    (hA : IsAlmostPalindrome w) (h1 : w.head? = some Letter.p) (h2 : w.getLast? = some Letter.q) :
    SimplyConnectedCells (stackedSites .vertical w) := by
  obtain ⟨hR, hL⟩ := small_vertical_rows w (mem_wordsUpTo hw) (almostPalB_of hA) h1 h2
  exact simplyConnectedCells_of_rows hR hL

end FLatticePaper.Tiles
