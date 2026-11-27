import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Tiles.AlmostTiling

/-! # Every vertex of a standard tile is a corner of one of its cells (H1)

A vertex set `P` has property `HasCornerCell P` when every point of `P` is a corner of a unit cell whose four corners
lie in `P`. This is the vertex form of the cell tile of `P` (`cellTileOf P` is the set of cells with all corners in `P`),
so `HasCornerCell P` says `P ⊆ (cellTileOf P).vertices`. The property is preserved by translation and union, and the
standard decomposition is built from translates and unions of the base tiles and the zero-one tiles, so it reduces to
the base tiles. -/

namespace FLatticePaper.Tiles.Standard

open FLatticePaper.Tiles

/-- Every point of `P` is a corner of a cell whose four corners lie in `P`. -/
def HasCornerCell (P : Finset GInt) : Prop :=
  ∀ x ∈ P, ∃ c : GInt, x ∈ cellCorners c ∧ ∀ y ∈ cellCorners c, y ∈ P

/-- The four corners of the cell with lower-left corner `c`, all in `p`. -/
def CellOK (p : GInt → Prop) (c : GInt) : Prop :=
  p c ∧ p (c + gOne) ∧ p (c + gI) ∧ p (c + (gOne + gI))

theorem mem_cellCorners_iff (c y : GInt) :
    y ∈ cellCorners c ↔ y = c ∨ y = c + gOne ∨ y = c + gI ∨ y = c + (gOne + gI) := by
  unfold cellCorners
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem hasCornerCell_shift {P : Finset GInt} (v : GInt) (h : HasCornerCell P) :
    HasCornerCell (P.image (· + v)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c, hc, hall⟩ := h y hy
  refine ⟨c + v, ?_, ?_⟩
  · rw [mem_cellCorners_iff] at hc ⊢
    rcases hc with rfl | rfl | rfl | rfl
    · left; rfl
    · right; left; abel
    · right; right; left; abel
    · right; right; right; abel
  · intro z hz
    rw [mem_cellCorners_iff] at hz
    rw [Finset.mem_image]
    refine ⟨z - v, hall (z - v) ?_, by abel⟩
    rw [mem_cellCorners_iff]
    rcases hz with rfl | rfl | rfl | rfl
    · left; abel
    · right; left; abel
    · right; right; left; abel
    · right; right; right; abel

theorem hasCornerCell_union {P Q : Finset GInt} (hP : HasCornerCell P) (hQ : HasCornerCell Q) :
    HasCornerCell (P ∪ Q) := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨c, hc, hall⟩ := hP x h
    exact ⟨c, hc, fun y hy => Finset.mem_union_left _ (hall y hy)⟩
  · obtain ⟨c, hc, hall⟩ := hQ x h
    exact ⟨c, hc, fun y hy => Finset.mem_union_right _ (hall y hy)⟩

/-- A predicate description of a vertex set with a covering by cells gives `HasCornerCell`. -/
theorem hasCornerCell_of_pred (S : Finset GInt) (p : GInt → Prop) (hS : ∀ x, x ∈ S ↔ p x)
    (hcov : ∀ x, p x → CellOK p x ∨ CellOK p (x - gOne) ∨ CellOK p (x - gI) ∨ CellOK p (x - (gOne + gI))) :
    HasCornerCell S := by
  intro x hx
  have hp : p x := (hS x).mp hx
  have key : ∀ c, CellOK p c → ∀ y ∈ cellCorners c, y ∈ S := by
    intro c hc y hy
    rw [mem_cellCorners_iff] at hy
    rw [hS]
    obtain ⟨h0, h1, h2, h3⟩ := hc
    rcases hy with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  rcases hcov x hp with h | h | h | h
  · exact ⟨x, by rw [mem_cellCorners_iff]; left; rfl, key x h⟩
  · exact ⟨x - gOne, by rw [mem_cellCorners_iff]; right; left; abel, key _ h⟩
  · exact ⟨x - gI, by rw [mem_cellCorners_iff]; right; right; left; abel, key _ h⟩
  · exact ⟨x - (gOne + gI), by rw [mem_cellCorners_iff]; right; right; right; abel, key _ h⟩

/-- The band of the near-one staircase: the linear part of `nstairF d`. -/
def bandP (d : ℤ) (a : GInt) : Prop :=
  0 ≤ a.1 ∧ a.1 ≤ d + 1 ∧ 1 ≤ a.2 ∧ a.2 ≤ 2 * d - 1 ∧ -1 ≤ a.2 - a.1 ∧ a.2 - a.1 ≤ d

/-- The near-one staircase as a predicate: the band and its two special points. -/
def nsP (d : ℤ) (a : GInt) : Prop := bandP d a ∨ a = (0, d + 1) ∨ a = (d + 1, d - 1)

/-- A cell all of whose corners lie in the band. -/
def bandCell (d : ℤ) (c : GInt) : Prop :=
  bandP d c ∧ bandP d (c + gOne) ∧ bandP d (c + gI) ∧ bandP d (c + (gOne + gI))

theorem cellOK_of_bandCell {d : ℤ} {c : GInt} (h : bandCell d c) : CellOK (nsP d) c :=
  ⟨Or.inl h.1, Or.inl h.2.1, Or.inl h.2.2.1, Or.inl h.2.2.2⟩

theorem nstairF_mem {d : ℤ} (hd : 2 ≤ d) (x : GInt) : x ∈ nstairF d ↔ nsP d x := by
  rw [mem_nstairF hd]
  simp only [nsP, bandP, Prod.ext_iff]

/-- The two special points of `nstairF d` each have a full cell inside `nstairF d`. -/
theorem nstairF_sp1 {d : ℤ} (hd : 2 ≤ d) : CellOK (nsP d) (0, d) := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inr (Or.inl ?_), Or.inl ?_⟩
  · simp only [bandP]
    omega
  · simp only [bandP, gOne, Prod.fst_add, Prod.snd_add]
    omega
  · simp [gI]
  · simp only [bandP, gOne, gI, Prod.fst_add, Prod.snd_add]
    omega

theorem nstairF_sp2 {d : ℤ} (hd : 2 ≤ d) : CellOK (nsP d) (d, d - 1) := by
  refine ⟨Or.inl ?_, Or.inr (Or.inr ?_), Or.inl ?_, Or.inl ?_⟩
  · simp only [bandP]
    omega
  · simp [gOne]
  · simp only [bandP, gI, Prod.fst_add, Prod.snd_add]
    omega
  · simp only [bandP, gOne, gI, Prod.fst_add, Prod.snd_add]
    omega

theorem nstairF_covering {d : ℤ} (hd : 2 ≤ d) (x : GInt) (hx : nsP d x) :
    CellOK (nsP d) x ∨ CellOK (nsP d) (x - gOne) ∨ CellOK (nsP d) (x - gI) ∨
      CellOK (nsP d) (x - (gOne + gI)) := by
  obtain ⟨x1, x2⟩ := x
  rcases hx with hb | hs | hs
  · have hb' : 0 ≤ x1 ∧ x1 ≤ d + 1 ∧ 1 ≤ x2 ∧ x2 ≤ 2 * d - 1 ∧ -1 ≤ x2 - x1 ∧ x2 - x1 ≤ d := hb
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb'
    rcases (show x2 - x1 = -1 ∨ x2 - x1 = d ∨ (-1 < x2 - x1 ∧ x2 - x1 < d) by omega) with hu | hu | hu
    · refine Or.inr (Or.inl (cellOK_of_bandCell ?_))
      unfold bandCell bandP gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega
    · refine Or.inr (Or.inr (Or.inl (cellOK_of_bandCell ?_)))
      unfold bandCell bandP gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega
    · rcases (show x1 ≤ d - 1 ∨ x1 = d ∨ x1 = d + 1 by omega) with hx1 | hx1 | hx1
      · refine Or.inl (cellOK_of_bandCell ?_)
        unfold bandCell bandP gOne gI
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      · rcases (show x2 ≤ 2 * d - 2 ∨ x2 = 2 * d - 1 by omega) with hx2 | hx2
        · refine Or.inl (cellOK_of_bandCell ?_)
          unfold bandCell bandP gOne gI
          simp only [Prod.fst_add, Prod.snd_add]
          omega
        · refine Or.inr (Or.inr (Or.inl (cellOK_of_bandCell ?_)))
          unfold bandCell bandP gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
      · rcases (show x2 = 2 * d - 1 ∨ x2 ≤ 2 * d - 2 by omega) with hx2 | hx2
        · refine Or.inr (Or.inr (Or.inr (cellOK_of_bandCell ?_)))
          unfold bandCell bandP gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
        · refine Or.inr (Or.inl (cellOK_of_bandCell ?_))
          unfold bandCell bandP gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
  · obtain ⟨rfl, rfl⟩ := hs
    right; right; left
    have e : ((0 : ℤ), d + 1) - gI = (0, d) := Prod.ext (by simp [gI]) (by simp [gI])
    rw [e]
    exact nstairF_sp1 hd
  · obtain ⟨rfl, rfl⟩ := hs
    right; left
    have e : (d + 1, d - 1) - gOne = (d, d - 1) := Prod.ext (by simp [gOne]) (by simp [gOne])
    rw [e]
    exact nstairF_sp2 hd

/-- The near-one staircase `nstairF d` (`lemma:basecase_2k_odd_std`) has every vertex a corner of a full cell, for `d ≥ 2`. -/
theorem nstairF_hasCornerCell {d : ℤ} (hd : 2 ≤ d) : HasCornerCell (nstairF d) :=
  hasCornerCell_of_pred (nstairF d) (nsP d) (fun x => nstairF_mem hd x)
    (fun x hx => nstairF_covering hd x hx)

/-! ### The base tile `stairF d` (`lemma:basecase_3k_even_std`) -/

/-- The linear part of `stairF d`. -/
def stB (d : ℤ) (a : GInt) : Prop :=
  2 - d ≤ a.1 ∧ a.1 ≤ d ∧ 0 ≤ a.2 ∧ a.2 ≤ d + 1 ∧ 1 ≤ a.1 + a.2 ∧ a.1 + a.2 ≤ d + 2

/-- `stairF d` as a predicate: the linear part and its two special points. -/
def stP (d : ℤ) (a : GInt) : Prop := stB d a ∨ a = (0, 0) ∨ a = (2, d + 1)

def stBCell (d : ℤ) (c : GInt) : Prop :=
  stB d c ∧ stB d (c + gOne) ∧ stB d (c + gI) ∧ stB d (c + (gOne + gI))

theorem cellOK_of_stBCell {d : ℤ} {c : GInt} (h : stBCell d c) : CellOK (stP d) c :=
  ⟨Or.inl h.1, Or.inl h.2.1, Or.inl h.2.2.1, Or.inl h.2.2.2⟩

theorem stairF_mem {d : ℤ} (hd : 2 ≤ d) (x : GInt) : x ∈ stairF d ↔ stP d x := by
  rw [mem_stairF hd]
  simp only [stP, stB, Prod.ext_iff]

/-- The special point `(0,0)` has the full cell `(0,0)` inside `stairF d`. -/
theorem stairF_sp0 {d : ℤ} (hd : 2 ≤ d) : CellOK (stP d) (0, 0) := by
  refine ⟨Or.inr (Or.inl rfl), Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
  · simp only [stB, gOne, Prod.fst_add, Prod.snd_add]
    omega
  · simp only [stB, gI, Prod.fst_add, Prod.snd_add]
    omega
  · simp only [stB, gOne, gI, Prod.fst_add, Prod.snd_add]
    omega

/-- The special point `(2,d+1)` has the full cell `(1,d)` inside `stairF d`. -/
theorem stairF_sp2 {d : ℤ} (hd : 2 ≤ d) : CellOK (stP d) (1, d) := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inr (Or.inr ?_)⟩
  · simp only [stB]
    omega
  · simp only [stB, gOne, Prod.fst_add, Prod.snd_add]
    omega
  · simp only [stB, gI, Prod.fst_add, Prod.snd_add]
    omega
  · simp [gOne, gI]

theorem stairF_covering {d : ℤ} (hd : 2 ≤ d) (x : GInt) (hx : stP d x) :
    CellOK (stP d) x ∨ CellOK (stP d) (x - gOne) ∨ CellOK (stP d) (x - gI) ∨
      CellOK (stP d) (x - (gOne + gI)) := by
  obtain ⟨x1, x2⟩ := x
  rcases hx with hb | hs | hs
  · have hb' : 2 - d ≤ x1 ∧ x1 ≤ d ∧ 0 ≤ x2 ∧ x2 ≤ d + 1 ∧ 1 ≤ x1 + x2 ∧ x1 + x2 ≤ d + 2 := hb
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb'
    rcases (show x2 ≤ d ∨ x2 = d + 1 by omega) with hy | hy
    · rcases (show x1 ≤ d - 1 ∨ x1 = d by omega) with hx1 | hx1
      · rcases (show x1 + x2 ≤ d ∨ x1 + x2 = d + 1 ∨ x1 + x2 = d + 2 by omega) with hs1 | hs1 | hs1
        · refine Or.inl (cellOK_of_stBCell ?_)
          unfold stBCell stB gOne gI
          simp only [Prod.fst_add, Prod.snd_add]
          omega
        · refine Or.inr (Or.inl (cellOK_of_stBCell ?_))
          unfold stBCell stB gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
        · refine Or.inr (Or.inr (Or.inr (cellOK_of_stBCell ?_)))
          unfold stBCell stB gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
      · rcases (show x2 ≤ 1 ∨ x2 = 2 by omega) with hx2 | hx2
        · refine Or.inr (Or.inl (cellOK_of_stBCell ?_))
          unfold stBCell stB gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
        · refine Or.inr (Or.inr (Or.inr (cellOK_of_stBCell ?_)))
          unfold stBCell stB gOne gI
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
          omega
    · rcases (show x1 ≤ 0 ∨ x1 = 1 by omega) with hx1 | hx1
      · refine Or.inr (Or.inr (Or.inl (cellOK_of_stBCell ?_)))
        unfold stBCell stB gOne gI
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        omega
      · refine Or.inr (Or.inr (Or.inr (cellOK_of_stBCell ?_)))
        unfold stBCell stB gOne gI
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
        omega
  · obtain ⟨rfl, rfl⟩ := hs
    exact Or.inl (stairF_sp0 hd)
  · obtain ⟨rfl, rfl⟩ := hs
    right; right; right
    have e : ((2 : ℤ), d + 1) - (gOne + gI) = (1, d) := Prod.ext (by simp [gOne, gI]) (by simp [gOne, gI])
    rw [e]
    exact stairF_sp2 hd

/-- The base tile `stairF d` has every vertex a corner of a full cell, for `d ≥ 2`. -/
theorem stairF_hasCornerCell {d : ℤ} (hd : 2 ≤ d) : HasCornerCell (stairF d) :=
  hasCornerCell_of_pred (stairF d) (stP d) (fun x => stairF_mem hd x)
    (fun x hx => stairF_covering hd x hx)

/-! ### The base tile `ladderF d` (`lemma:basecase_3k_odd_std`) -/

/-- The linear part of `ladderF d`: the strip `C`. -/
def laCL (d : ℤ) (a : GInt) : Prop :=
  2 - d ≤ a.1 ∧ a.1 ≤ 2 * d ∧ 0 ≤ a.2 ∧ a.2 ≤ d + 2 ∧ 1 ≤ a.1 + a.2 ∧ a.1 + a.2 ≤ 2 * d + 3

/-- The exclusions of `ladderF d`: the bottom-right and top-left corner pieces. -/
def laX (d : ℤ) (a : GInt) : Prop := ¬((d ≤ a.1 ∧ a.2 = 0) ∨ (a.1 ≤ 2 ∧ a.2 = d + 2))

/-- `ladderF d` as a predicate: the two special points, the diagonal `B`, the strip `C`, minus the exclusions. -/
def laP (d : ℤ) (a : GInt) : Prop :=
  ((a.1 = 0 ∧ a.2 = 0) ∨ (a.1 = d + 2 ∧ a.2 = d + 2) ∨ (a.1 + a.2 = d + 2 ∧ 1 < a.2 ∧ a.2 < d + 1) ∨
    laCL d a) ∧ laX d a

/-- A cell whose four corners are in the strip and avoid the exclusions. -/
def laOK (d : ℤ) (c : GInt) : Prop :=
  laCL d c ∧ laCL d (c + gOne) ∧ laCL d (c + gI) ∧ laCL d (c + (gOne + gI)) ∧
    laX d c ∧ laX d (c + gOne) ∧ laX d (c + gI) ∧ laX d (c + (gOne + gI))

theorem laOK_cellOK {d : ℤ} {c : GInt} (h : laOK d c) : CellOK (laP d) c :=
  ⟨⟨Or.inr (Or.inr (Or.inr h.1)), h.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.1)), h.2.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.2.1)), h.2.2.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.2.2.1)), h.2.2.2.2.2.2.2⟩⟩

theorem ladderF_mem {d : ℤ} (hd : 2 ≤ d) (x : GInt) : x ∈ ladderF d ↔ laP d x :=
  mem_ladderF hd x

/-- The covering of the strip part of `ladderF d` (`3 ≤ d`). -/
theorem laBand_cover {d : ℤ} (hd : 3 ≤ d) (x1 x2 : ℤ) (hC : laCL d (x1, x2)) (hX : laX d (x1, x2)) :
    CellOK (laP d) (x1, x2) ∨ CellOK (laP d) ((x1, x2) - gOne) ∨ CellOK (laP d) ((x1, x2) - gI) ∨
      CellOK (laP d) ((x1, x2) - (gOne + gI)) := by
  have hC' : 2 - d ≤ x1 ∧ x1 ≤ 2 * d ∧ 0 ≤ x2 ∧ x2 ≤ d + 2 ∧ 1 ≤ x1 + x2 ∧ x1 + x2 ≤ 2 * d + 3 := hC
  have hX' : ¬((d ≤ x1 ∧ x2 = 0) ∨ (x1 ≤ 2 ∧ x2 = d + 2)) := hX
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hC'
  rcases (show x2 = 0 ∨ (1 ≤ x2 ∧ x2 ≤ d) ∨ x2 = d + 1 ∨ x2 = d + 2 by omega) with r0 | rmid | r1 | r2
  · subst r0
    rcases (show x1 = 1 ∨ 2 ≤ x1 by omega) with q1 | q1
    · subst q1
      exact Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega))
    · exact Or.inr (Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega)))
  · rcases (show (x1 ≤ 2 * d - 1 ∧ x1 + x2 ≤ 2 * d + 1) ∨ (x1 ≤ 2 * d - 1 ∧ 2 * d + 2 ≤ x1 + x2) ∨
        (x1 = 2 * d ∧ x2 ≤ 2) ∨ (x1 = 2 * d ∧ x2 = 3) by omega) with q | q | q | q
    · exact Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega))
    · exact Or.inr (Or.inr (Or.inr (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))
    · exact Or.inr (Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega)))
    · exact Or.inr (Or.inr (Or.inr (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))
  · rcases (show x1 ≤ d + 1 ∨ x1 = d + 2 by omega) with q | q
    · exact Or.inr (Or.inr (Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))
    · subst q
      exact Or.inr (Or.inr (Or.inr (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))
  · subst r2
    rcases (show x1 ≤ d ∨ x1 = d + 1 by omega) with q | q
    · exact Or.inr (Or.inr (Or.inl (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))
    · subst q
      exact Or.inr (Or.inr (Or.inr (laOK_cellOK (by unfold laOK laCL laX gOne gI; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]; omega))))

/-- The two special points of `ladderF d`: the cell `(0,0)` and the cell `(d+1,d+1)`. -/
theorem laSpec0 {d : ℤ} (hd : 3 ≤ d) : CellOK (laP d) (0, 0) := by
  refine ⟨⟨Or.inl ⟨rfl, rfl⟩, ?_⟩, ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩, ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩,
    ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩⟩ <;>
    simp only [laCL, laX, gOne, gI, Prod.fst_add, Prod.snd_add] <;> omega

theorem laSpecD {d : ℤ} (hd : 3 ≤ d) : CellOK (laP d) (d + 1, d + 1) := by
  refine ⟨⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩, ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩,
    ⟨Or.inr (Or.inr (Or.inr ?_)), ?_⟩, ⟨Or.inr (Or.inl ⟨?_, ?_⟩), ?_⟩⟩ <;>
    simp only [laCL, laX, gOne, gI, Prod.fst_add, Prod.snd_add] <;> omega

theorem ladderF_covering {d : ℤ} (hd : 3 ≤ d) (x : GInt) (hx : laP d x) :
    CellOK (laP d) x ∨ CellOK (laP d) (x - gOne) ∨ CellOK (laP d) (x - gI) ∨
      CellOK (laP d) (x - (gOne + gI)) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨hD, hX⟩ := hx
  rcases hD with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | hC
  · have h1 : x1 = 0 := e1
    have h2 : x2 = 0 := e2
    subst h1; subst h2
    exact Or.inl (laSpec0 hd)
  · have h1 : x1 = d + 2 := e1
    have h2 : x2 = d + 2 := e2
    subst h1; subst h2
    refine Or.inr (Or.inr (Or.inr ?_))
    have e : (d + 2, d + 2) - (gOne + gI) = (d + 1, d + 1) := Prod.ext (by simp [gOne, gI]; omega) (by simp [gOne, gI]; omega)
    rw [e]
    exact laSpecD hd
  · have hC2 : laCL d (x1, x2) := by
      have f1 : x1 + x2 = d + 2 := e1
      have f2 : 1 < x2 := e2
      have f3 : x2 < d + 1 := e3
      unfold laCL
      simp only
      omega
    exact laBand_cover hd x1 x2 hC2 hX
  · exact laBand_cover hd x1 x2 hC hX

/-- The base tile `ladderF d` (`lemma:basecase_3k_odd_std`) has every vertex a corner of a full cell, for `d ≥ 3`. -/
theorem ladderF_hasCornerCell {d : ℤ} (hd : 3 ≤ d) : HasCornerCell (ladderF d) :=
  hasCornerCell_of_pred (ladderF d) (laP d) (fun x => ladderF_mem (by omega) x)
    (fun x hx => ladderF_covering hd x hx)

/-! ### The base tile `nladderF d` -/

/-- The band of `nladderF d`. -/
def nlaCL (d : ℤ) (a : GInt) : Prop :=
  -1 ≤ a.1 ∧ a.1 ≤ d + 1 ∧ 1 ≤ a.2 ∧ a.2 ≤ 3 * d - 1 ∧ -1 ≤ a.2 - a.1 ∧ a.2 - a.1 ≤ 2 * d + 1

/-- The exclusions of `nladderF d`. -/
def nlaX (d : ℤ) (a : GInt) : Prop := ¬((a.1 = -1 ∧ a.2 ≤ d + 1) ∨ (a.1 = d + 1 ∧ 2 * d - 1 ≤ a.2))

/-- `nladderF d` as a predicate: the two special points, the diagonal, the band, minus the exclusions. -/
def nlaP (d : ℤ) (a : GInt) : Prop :=
  ((a.1 = -1 ∧ a.2 = 2 * d + 1) ∨ (a.1 = d + 1 ∧ a.2 = d - 1) ∨ (a.2 - a.1 = d ∧ 0 < a.1 ∧ a.1 < d) ∨
    nlaCL d a) ∧ nlaX d a

/-- A cell whose four corners lie in the band and avoid the exclusions. -/
def nlaOK (d : ℤ) (c : GInt) : Prop :=
  nlaCL d c ∧ nlaCL d (c + gOne) ∧ nlaCL d (c + gI) ∧ nlaCL d (c + (gOne + gI)) ∧
    nlaX d c ∧ nlaX d (c + gOne) ∧ nlaX d (c + gI) ∧ nlaX d (c + (gOne + gI))

theorem nlaOK_cellOK {d : ℤ} {c : GInt} (h : nlaOK d c) : CellOK (nlaP d) c :=
  ⟨⟨Or.inr (Or.inr (Or.inr h.1)), h.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.1)), h.2.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.2.1)), h.2.2.2.2.2.2.1⟩,
    ⟨Or.inr (Or.inr (Or.inr h.2.2.2.1)), h.2.2.2.2.2.2.2⟩⟩

theorem nladderF_mem {d : ℤ} (hd : 2 ≤ d) (x : GInt) : x ∈ nladderF d ↔ nlaP d x :=
  mem_nladderF hd x

/-- The covering of the band part of `nladderF d` (`3 ≤ d`), by the decision list
on the diagonal coordinate `x₂ - x₁` and the top row. -/
theorem nladderF_band_cover {d : ℤ} (hd : 3 ≤ d) (x1 x2 : ℤ) (hC : nlaCL d (x1, x2))
    (hX : nlaX d (x1, x2)) :
    CellOK (nlaP d) (x1, x2) ∨ CellOK (nlaP d) ((x1, x2) - gOne) ∨
      CellOK (nlaP d) ((x1, x2) - gI) ∨ CellOK (nlaP d) ((x1, x2) - (gOne + gI)) := by
  have hC' : -1 ≤ x1 ∧ x1 ≤ d + 1 ∧ 1 ≤ x2 ∧ x2 ≤ 3 * d - 1 ∧ -1 ≤ x2 - x1 ∧ x2 - x1 ≤ 2 * d + 1 := hC
  have hX' : ¬((x1 = -1 ∧ x2 ≤ d + 1) ∨ (x1 = d + 1 ∧ 2 * d - 1 ≤ x2)) := hX
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hC'
  by_cases r1 : x2 - x1 = -1
  · exact Or.inr (Or.inl (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega)))
  by_cases r2 : x2 - x1 = 2 * d + 1
  · exact Or.inr (Or.inr (Or.inl (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega))))
  by_cases r3 : x2 = 3 * d - 1
  · exact Or.inr (Or.inr (Or.inr (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega))))
  by_cases r5 : x1 = d + 1 ∧ d + 1 ≤ x2 ∧ x2 ≤ 2 * d - 2
  · exact Or.inr (Or.inr (Or.inr (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega))))
  by_cases r6 : x1 = d ∧ 2 * d - 2 ≤ x2
  · exact Or.inr (Or.inr (Or.inr (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
      omega))))
  by_cases r7 : x1 = d ∧ x2 ≤ 2 * d - 3
  · exact Or.inl (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_add, Prod.snd_add]
      omega))
  · exact Or.inl (nlaOK_cellOK (by
      unfold nlaOK nlaCL nlaX gOne gI
      simp only [Prod.fst_add, Prod.snd_add]
      omega))

/-- The cell `(-1,2d)`, which is the cell of the special point `(-1,2d+1)`. -/
theorem nlaS1 {d : ℤ} (hd : 3 ≤ d) : CellOK (nlaP d) (-1, 2 * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL; simp only; omega))),
      by unfold nlaX; simp only; omega⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL gOne; simp only [Prod.fst_add, Prod.snd_add]; omega))),
      by unfold nlaX gOne; simp only [Prod.fst_add, Prod.snd_add]; omega⟩
  · exact ⟨Or.inl ⟨by simp [gI], by simp [gI]⟩, by unfold nlaX gI; simp only [Prod.fst_add, Prod.snd_add]; omega⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega))),
      by unfold nlaX gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega⟩

/-- The cell `(d,d-1)`, which is the cell of the special point `(d+1,d-1)`. -/
theorem nlaS2 {d : ℤ} (hd : 3 ≤ d) : CellOK (nlaP d) (d, d - 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL; simp only; omega))),
      by unfold nlaX; simp only; omega⟩
  · exact ⟨Or.inr (Or.inl ⟨by simp [gOne], by simp [gOne]⟩), by unfold nlaX gOne; simp only [Prod.fst_add, Prod.snd_add]; omega⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL gI; simp only [Prod.fst_add, Prod.snd_add]; omega))),
      by unfold nlaX gI; simp only [Prod.fst_add, Prod.snd_add]; omega⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (by unfold nlaCL gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega))),
      by unfold nlaX gOne gI; simp only [Prod.fst_add, Prod.snd_add]; omega⟩

theorem nladderF_covering {d : ℤ} (hd : 3 ≤ d) (x : GInt) (hx : nlaP d x) :
    CellOK (nlaP d) x ∨ CellOK (nlaP d) (x - gOne) ∨ CellOK (nlaP d) (x - gI) ∨
      CellOK (nlaP d) (x - (gOne + gI)) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨hD, hX⟩ := hx
  rcases hD with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | hC
  · -- the special point (-1,2d+1): its cell is (-1,2d) = x - gI
    have h1 : x1 = -1 := e1
    have h2 : x2 = 2 * d + 1 := e2
    subst h1; subst h2
    refine Or.inr (Or.inr (Or.inl ?_))
    have e : ((-1 : ℤ), 2 * d + 1) - gI = (-1, 2 * d) := Prod.ext (by simp [gI]) (by simp [gI])
    rw [e]
    exact nlaS1 hd
  · -- the special point (d+1,d-1): its cell is (d,d-1) = x - gOne
    have h1 : x1 = d + 1 := e1
    have h2 : x2 = d - 1 := e2
    subst h1; subst h2
    refine Or.inr (Or.inl ?_)
    have e : ((d + 1 : ℤ), d - 1) - gOne = (d, d - 1) := Prod.ext (by simp [gOne]) (by simp [gOne])
    rw [e]
    exact nlaS2 hd
  · have hC2 : nlaCL d (x1, x2) := by
      unfold nlaCL
      simp only
      omega
    exact nladderF_band_cover hd x1 x2 hC2 hX
  · exact nladderF_band_cover hd x1 x2 hC hX

/-- The base tile `nladderF d` has every vertex a corner of a full cell, for `d ≥ 3`. -/
theorem nladderF_hasCornerCell {d : ℤ} (hd : 3 ≤ d) : HasCornerCell (nladderF d) :=
  hasCornerCell_of_pred (nladderF d) (nlaP d) (fun x => nladderF_mem (by omega) x)
    (fun x hx => nladderF_covering hd x hx)

/-! ### The zero-one tiles, and the register invariant -/

theorem zeroTile_hcc : HasCornerCell zeroTile := by
  intro x hx
  have hx' : x ∈ ({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)} : Finset GInt) := hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 1), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 1), by decide, by decide⟩

theorem oneTile_hcc : HasCornerCell oneTile := by
  intro x hx
  have hx' : x ∈ ({(0, 0), (0, 1), (1, 0), (1, 1)} : Finset GInt) := hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl | rfl | rfl
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩
  · exact ⟨(0, 0), by decide, by decide⟩

theorem nstairN_hcc {d : ℤ} (hd : 2 ≤ d) : HasCornerCell (nstairN d) :=
  hasCornerCell_shift (0, -1) (nstairF_hasCornerCell hd)

theorem nladderN_hcc {d : ℤ} (hd : 3 ≤ d) : HasCornerCell (nladderN d) :=
  hasCornerCell_shift (0, -1) (nladderF_hasCornerCell hd)

theorem oddChildB_hcc (b : Bool) (T1 T2 : Tile) (p q : Farey.Fraction) (h1 : HasCornerCell T1)
    (h2 : HasCornerCell T2) : HasCornerCell (oddChildB b T1 T2 p q) := by
  cases b <;> simp only [oddChildB] <;>
    repeat' (first | exact h1 | exact h2 | apply hasCornerCell_union | apply hasCornerCell_shift)

theorem evenChildB_hcc (b : Bool) (T1 T2 : Tile) (p q : Farey.Fraction) (h1 : HasCornerCell T1)
    (h2 : HasCornerCell T2) : HasCornerCell (evenChildB b T1 T2 p q) := by
  cases b <;> simp only [evenChildB] <;>
    repeat' (first | exact h1 | exact h2 | apply hasCornerCell_union | apply hasCornerCell_shift)

/-- The tiles of the children of any word, from registers with H1, have H1. -/
theorem childTiles_hcc {w : Farey.Word} {s : TState} (h1 : HasCornerCell s.tOdd) (h2 : HasCornerCell s.tEven) :
    HasCornerCell (childTiles w s).1 ∧ HasCornerCell (childTiles w s).2 := by
  unfold childTiles
  by_cases hA : w = []
  · rw [if_pos hA]
    exact ⟨nstairN_hcc (by norm_num), stairF_hasCornerCell (by norm_num)⟩
  rw [if_neg hA]
  have hl : (1 : ℤ) ≤ (w.length : ℤ) := by
    cases w with
    | nil => exact absurd rfl hA
    | cons a t => simp only [List.length_cons]; omega
  by_cases hB : w = List.replicate w.length Farey.Digit.three
  · rw [if_pos hB]
    exact ⟨ladderF_hasCornerCell (by omega), stairF_hasCornerCell (by omega)⟩
  rw [if_neg hB]
  by_cases hC : w = List.replicate w.length Farey.Digit.two
  · rw [if_pos hC]
    exact ⟨nstairN_hcc (by omega), nladderN_hcc (by omega)⟩
  rw [if_neg hC]
  exact ⟨oddChildB_hcc _ _ _ _ _ h1 h2, evenChildB_hcc _ _ _ _ _ h1 h2⟩

/-- The two registers of a state both have H1. -/
def RegHCC (s : TState) : Prop := HasCornerCell s.tOdd ∧ HasCornerCell s.tEven

theorem stepState_hcc {pre : Farey.Word} {s : TState} {d : Farey.Digit} (h : RegHCC s) : RegHCC (stepState pre s d) := by
  obtain ⟨h1, h2⟩ := h
  have hc := childTiles_hcc (w := pre) (s := s) h1 h2
  rcases d with _ | _ | _
  all_goals first
    | exact ⟨hc.1, hc.2⟩
    | exact ⟨hc.1, h2⟩
    | exact ⟨h1, hc.2⟩

theorem runFrom_hcc (rest : Farey.Word) : ∀ (pre : Farey.Word) (s : TState), RegHCC s → RegHCC (runFrom pre rest s) := by
  induction rest with
  | nil => intro pre s h; exact h
  | cons d rest ih => intro pre s h; exact ih (pre ++ [d]) (stepState pre s d) (stepState_hcc h)

theorem stateAt_hcc (w : Farey.Word) : RegHCC (stateAt w) :=
  runFrom_hcc w [] initState ⟨zeroTile_hcc, oneTile_hcc⟩

/-- Every standard tile of an odd child has H1 (every point is a corner of a cell of the tile). -/
theorem oddTile_hcc (w : Farey.Word) : HasCornerCell (oddTile w) :=
  (childTiles_hcc (w := w) (s := stateAt w) (stateAt_hcc w).1 (stateAt_hcc w).2).1

/-- Every standard tile of an even child has H1. -/
theorem evenTile_hcc (w : Farey.Word) : HasCornerCell (evenTile w) :=
  (childTiles_hcc (w := w) (s := stateAt w) (stateAt_hcc w).1 (stateAt_hcc w).2).2

end FLatticePaper.Tiles.Standard
