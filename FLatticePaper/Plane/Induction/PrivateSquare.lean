import FLatticePaper.Plane.Induction.SquareClauses
import FLatticePaper.Plane.Induction.SignedPolicy

/-! # The private square of a forced white (generic)

A forced non-seed white `c` is forced by a unit square `S = squareCorners a b` (`ForcedEdge.unit`): `c ∈ S`, its rejected input lies
outside `S`, and every other corner `c'` of `S` is black or a forced white whose forced input lies in `S`. In a unit square each corner
has exactly one input inside `S` (the horizontal one at an even site, the vertical one at an odd site), and these inputs form a single
4-cycle on the corners. A retained policy that keeps the inputs of every black corner (quota) and every forced edge (`forcedRetained`)
keeps each corner `c' ≠ c` on its in-square input; following these retained edges from `c'` goes round the square and reaches `c`.

This gives the field `privateSquare` of `OldPolicyWitness` from the forcing data alone. -/

namespace FLatticePaper.PrivateSquare

open FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The input of the corner `y` of the unit square at `(a, b)` that lies inside the square. -/
def nxtS (a b : ℤ) (y : Site) : Site :=
  if EvenSite y then (if y.1 = a then (a + 1, y.2) else (a, y.2))
  else (if y.2 = b then (y.1, b + 1) else (y.1, b))

theorem mem_square_coords {a b : ℤ} {y : Site} :
    y ∈ squareCorners a b ↔ (y.1 = a ∨ y.1 = a + 1) ∧ (y.2 = b ∨ y.2 = b + 1) := by
  obtain ⟨y1, y2⟩ := y
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem incomingNeg_even {y : Site} (he : EvenSite y) : incomingNeg y = (y.1 - 1, y.2) := by
  simp [incomingNeg, he]

theorem incomingPos_even {y : Site} (he : EvenSite y) : incomingPos y = (y.1 + 1, y.2) := by
  simp [incomingPos, he]

theorem incomingNeg_odd {y : Site} (he : ¬ EvenSite y) : incomingNeg y = (y.1, y.2 - 1) := by
  simp [incomingNeg, he]

theorem incomingPos_odd {y : Site} (he : ¬ EvenSite y) : incomingPos y = (y.1, y.2 + 1) := by
  simp [incomingPos, he]

theorem nxtS_even {a b : ℤ} {y : Site} (he : EvenSite y) :
    nxtS a b y = if y.1 = a then (a + 1, y.2) else (a, y.2) := by
  simp [nxtS, he]

theorem nxtS_odd {a b : ℤ} {y : Site} (he : ¬ EvenSite y) :
    nxtS a b y = if y.2 = b then (y.1, b + 1) else (y.1, b) := by
  simp [nxtS, he]

theorem nxtS_mem {a b : ℤ} {y : Site} (hy : y ∈ squareCorners a b) : nxtS a b y ∈ squareCorners a b := by
  rw [mem_square_coords] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  by_cases he : EvenSite y
  · rw [nxtS_even he]
    split_ifs <;> dsimp only <;> omega
  · rw [nxtS_odd he]
    split_ifs <;> dsimp only <;> omega

theorem nxtS_isInput {a b : ℤ} {y : Site} (hy : y ∈ squareCorners a b) :
    nxtS a b y = incomingNeg y ∨ nxtS a b y = incomingPos y := by
  rw [mem_square_coords] at hy
  obtain ⟨hy1, hy2⟩ := hy
  by_cases he : EvenSite y
  · rw [nxtS_even he, incomingNeg_even he, incomingPos_even he]
    split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega
  · rw [nxtS_odd he, incomingNeg_odd he, incomingPos_odd he]
    split_ifs <;> simp only [Prod.mk.injEq, true_and] <;> omega

/-- The only input of a corner of the square that lies in the square is its in-square input. -/
theorem eq_nxtS_of_input {a b : ℤ} {y y' : Site} (hy : y ∈ squareCorners a b) (hy' : y' ∈ squareCorners a b)
    (h : y' = incomingNeg y ∨ y' = incomingPos y) : y' = nxtS a b y := by
  rw [mem_square_coords] at hy hy'
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hy1', hy2'⟩ := hy'
  by_cases he : EvenSite y
  · rw [nxtS_even he]
    rw [incomingNeg_even he, incomingPos_even he] at h
    rcases h with rfl | rfl <;> dsimp only at hy1' hy2' <;> split_ifs <;> simp only [Prod.mk.injEq, and_true] <;> omega
  · rw [nxtS_odd he]
    rw [incomingNeg_odd he, incomingPos_odd he] at h
    rcases h with rfl | rfl <;> dsimp only at hy1' hy2' <;> split_ifs <;> simp only [Prod.mk.injEq, true_and] <;> omega

/-- The in-square successor on an even-base square. -/
theorem nxt_table_even {a b : ℤ} (hp : (a + b) % 2 = 0) :
    nxtS a b (a, b) = (a + 1, b) ∧ nxtS a b (a + 1, b) = (a + 1, b + 1) ∧
      nxtS a b (a + 1, b + 1) = (a, b + 1) ∧ nxtS a b (a, b + 1) = (a, b) := by
  have e1 : EvenSite (a, b) := hp
  have e2 : ¬ EvenSite (a + 1, b) := by unfold EvenSite; dsimp only; omega
  have e3 : EvenSite (a + 1, b + 1) := by unfold EvenSite; dsimp only; omega
  have e4 : ¬ EvenSite (a, b + 1) := by unfold EvenSite; dsimp only; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nxtS_even e1, if_pos rfl]
  · rw [nxtS_odd e2, if_pos rfl]
  · rw [nxtS_even e3, if_neg (by dsimp only; omega)]
  · rw [nxtS_odd e4, if_neg (by dsimp only; omega)]

/-- The in-square successor on an odd-base square. -/
theorem nxt_table_odd {a b : ℤ} (hp : (a + b) % 2 = 1) :
    nxtS a b (a, b) = (a, b + 1) ∧ nxtS a b (a, b + 1) = (a + 1, b + 1) ∧
      nxtS a b (a + 1, b + 1) = (a + 1, b) ∧ nxtS a b (a + 1, b) = (a, b) := by
  have e1 : ¬ EvenSite (a, b) := by unfold EvenSite; dsimp only; omega
  have e2 : EvenSite (a, b + 1) := by unfold EvenSite; dsimp only; omega
  have e3 : ¬ EvenSite (a + 1, b + 1) := by unfold EvenSite; dsimp only; omega
  have e4 : EvenSite (a + 1, b) := by unfold EvenSite; dsimp only; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nxtS_odd e1, if_pos rfl]
  · rw [nxtS_even e2, if_pos rfl]
  · rw [nxtS_odd e3, if_neg (by dsimp only; omega)]
  · rw [nxtS_even e4, if_neg (by dsimp only; omega)]

/-- The four corners lie on the 4-cycle of in-square successors: from any corner, the square's corners are reached in at most three
steps. -/
theorem cover_of_square {a b : ℤ} {x c : Site} (hx : x ∈ squareCorners a b) (hc : c ∈ squareCorners a b) :
    c = x ∨ c = nxtS a b x ∨ c = nxtS a b (nxtS a b x) ∨ c = nxtS a b (nxtS a b (nxtS a b x)) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  rw [mem_square_coords] at hx hc
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hc1, hc2⟩ := hc
  dsimp only at hx1 hx2 hc1 hc2 ⊢
  by_cases hp : (a + b) % 2 = 0
  · obtain ⟨t1, t2, t3, t4⟩ := nxt_table_even hp
    rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [t1, t2, t3, t4, Prod.mk.injEq, and_true, true_and, true_or, or_true]
  · obtain ⟨t1, t2, t3, t4⟩ := nxt_table_odd (show (a + b) % 2 = 1 by omega)
    rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [t1, t2, t3, t4, Prod.mk.injEq, and_true, true_and, true_or, or_true]

/-- The walk: from a corner `x ≠ c` of the square, the retained in-square steps reach `c`. -/
theorem walk_of_square (R : Site → Site → Prop) {a b : ℤ} {c : Site} (hc : c ∈ squareCorners a b)
    (hstep : ∀ y ∈ squareCorners a b, y ≠ c → R y (nxtS a b y)) {x : Site} (hx : x ∈ squareCorners a b) (hxc : x ≠ c) :
    Relation.TransGen R x c := by
  have s1 := hstep x hx hxc
  by_cases e1 : nxtS a b x = c
  · rw [e1] at s1
    exact Relation.TransGen.single s1
  have h1 := nxtS_mem hx
  have s2 := hstep _ h1 e1
  by_cases e2 : nxtS a b (nxtS a b x) = c
  · rw [e2] at s2
    exact Relation.TransGen.tail (Relation.TransGen.single s1) s2
  have h2 := nxtS_mem h1
  have s3 := hstep _ h2 e2
  by_cases e3 : nxtS a b (nxtS a b (nxtS a b x)) = c
  · rw [e3] at s3
    exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single s1) s2) s3
  exfalso
  rcases cover_of_square hx hc with h | h | h | h
  · exact hxc h.symm
  · exact e1 h.symm
  · exact e2 h.symm
  · exact e3 h.symm

/-- **The private square of a forced white.** For a forced non-seed edge `c → i` of the field `G` under the retained edges, with the
black quota and the forced edges retained, there is a unit square containing `c` whose other corners reach `c` along retained edges
(each step a retained input of the site before it). -/
theorem private_square_of_forced {G : Field} {seed : Site → Site → Prop} {retained : Site → Site → Prop}
    (hquota : RetainQuota G retained) (hfr : ∀ c i, ForcedEdge G seed c i → retained c i)
    {c i : Site} (hF : ForcedEdge G seed c i) (hns : ¬ seed c i) :
    ∃ a b : ℤ, c ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ c → Relation.TransGen (fun x y => retained x y ∧ Edge y x) c' c := by
  unfold RetainQuota at hquota
  obtain ⟨hq1, _⟩ := hquota
  cases hF with
  | seed hs => exact absurd hs hns
  | @unit a b _ _ inside hc _ _ _ hin hforced =>
    refine ⟨a, b, hc, fun c' hc' hne => walk_of_square (fun x y => retained x y ∧ Edge y x) hc ?_ hc' hne⟩
    intro y hy hyc
    have hret : retained y (nxtS a b y) := by
      rcases hin y hy hyc with hb | ⟨hw0, hmem, hins⟩
      · obtain ⟨hn, hp⟩ := hq1 y hb
        rcases nxtS_isInput hy with h | h
        · rw [h]; exact hn
        · rw [h]; exact hp
      · have hr := hfr y (inside y) (hforced y hy hyc hw0)
        rw [← eq_nxtS_of_input hy hmem hins]
        exact hr
    exact ⟨hret, nxtS_isInput hy⟩

end FLatticePaper.PrivateSquare
