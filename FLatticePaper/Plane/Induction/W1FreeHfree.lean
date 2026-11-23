import FLatticePaper.Plane.Induction.W1FreeSquare
import FLatticePaper.Plane.Induction.W1FreeDescent
import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.W1NonfreeHsqC

/-! # Task 95: the free parent roots' `ParentSquareOut` from the free-root table (the lead's `hfree`)

`RowSq R S z` is the row of the free table: a unit square `Q ∋ z` whose other corners `p0, p1, p2` form the retained chain
`p0 → p1 → p2 → z` with `p0` the rejected input, all three in `S` (the hypotheses of `free_forced_of_descent`). The seven shapes of
`W1FreeSquare` (S1..S7, by parity of `z`) give the rows explicitly (`rowSq_S1` ... `rowSq_S7`). `TableShape R S z` is the table's content:
for the free root `z` one of the seven shapes holds, with its three retained edges and its chain points in `S`. The retained edges of the
bulk rows are the fan facts (named, inside `TableShape`).

From the table, `free_forced_of_descent` gives a forced edge at each free white root of `S` (given a rank bound `B` on `S`), and
`parentSquareOut_of_forced` turns it into `ParentSquareOut`. So `hfree` reduces to the named inputs `TableShape` and the rank bound. -/

set_option linter.unusedSimpArgs false

namespace FLatticePaper.W1FreeHfree

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1NonfreeOut FLatticePaper.W1SheetSquare

/-- A free-root row: a unit square `Q ∋ z` with corners `p0, p1, p2` forming the retained chain `p0 → p1 → p2 → z`, `p0` an input of `z`,
the three chain points in `S`. -/
def RowSq (R : Site → Site → Prop) (S : Set Site) (z : Site) : Prop :=
  ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
    z ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
    (∀ c' ∈ squareCorners a b, c' ≠ z → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
    p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg z ∨ p0 = incomingPos z) ∧
    (p0 ∈ S ∧ p1 ∈ S ∧ p2 ∈ S) ∧
    Edge p1 p0 ∧ Edge p2 p1 ∧ Edge z p2 ∧
    R p0 p1 ∧ R p1 p2 ∧ R p2 z

theorem rowSq_S1 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 + 1) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1 + 1, z2) ∈ S)
    (hR0 : R (z1, z2 + 1) (z1 + 1, z2 + 1)) (hR1 : R (z1 + 1, z2 + 1) (z1 + 1, z2)) (hR2 : R (z1 + 1, z2) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1, z2 + 1), (z1 + 1, z2 + 1), (z1 + 1, z2), z1, z2,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S2 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hS : (z1 + 1, z2) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1, z2 + 1) ∈ S)
    (hR0 : R (z1 + 1, z2) (z1 + 1, z2 + 1)) (hR1 : R (z1 + 1, z2 + 1) (z1, z2 + 1)) (hR2 : R (z1, z2 + 1) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1 + 1, z2), (z1 + 1, z2 + 1), (z1, z2 + 1), z1, z2,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S3 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hS : (z1 + 1, z2) ∈ S ∧ (z1 + 1, z2 - 1) ∈ S ∧ (z1, z2 - 1) ∈ S)
    (hR0 : R (z1 + 1, z2) (z1 + 1, z2 - 1)) (hR1 : R (z1 + 1, z2 - 1) (z1, z2 - 1)) (hR2 : R (z1, z2 - 1) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1 + 1, z2), (z1 + 1, z2 - 1), (z1, z2 - 1), z1, z2 - 1,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S4 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 - 1) ∈ S ∧ (z1 + 1, z2 - 1) ∈ S ∧ (z1 + 1, z2) ∈ S)
    (hR0 : R (z1, z2 - 1) (z1 + 1, z2 - 1)) (hR1 : R (z1 + 1, z2 - 1) (z1 + 1, z2)) (hR2 : R (z1 + 1, z2) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1, z2 - 1), (z1 + 1, z2 - 1), (z1 + 1, z2), z1, z2 - 1,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S5 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hS : (z1 - 1, z2) ∈ S ∧ (z1 - 1, z2 + 1) ∈ S ∧ (z1, z2 + 1) ∈ S)
    (hR0 : R (z1 - 1, z2) (z1 - 1, z2 + 1)) (hR1 : R (z1 - 1, z2 + 1) (z1, z2 + 1)) (hR2 : R (z1, z2 + 1) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1 - 1, z2), (z1 - 1, z2 + 1), (z1, z2 + 1), z1 - 1, z2,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S6 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 + 1) ∈ S ∧ (z1 - 1, z2 + 1) ∈ S ∧ (z1 - 1, z2) ∈ S)
    (hR0 : R (z1, z2 + 1) (z1 - 1, z2 + 1)) (hR1 : R (z1 - 1, z2 + 1) (z1 - 1, z2)) (hR2 : R (z1 - 1, z2) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1, z2 + 1), (z1 - 1, z2 + 1), (z1 - 1, z2), z1 - 1, z2,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

theorem rowSq_S7 {R : Site → Site → Prop} (S : Set Site) (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hS : (z1, z2 - 1) ∈ S ∧ (z1 - 1, z2 - 1) ∈ S ∧ (z1 - 1, z2) ∈ S)
    (hR0 : R (z1, z2 - 1) (z1 - 1, z2 - 1)) (hR1 : R (z1 - 1, z2 - 1) (z1 - 1, z2)) (hR2 : R (z1 - 1, z2) (z1, z2)) :
    RowSq R S (z1, z2) := by
  refine ⟨(z1, z2 - 1), (z1 - 1, z2 - 1), (z1 - 1, z2), z1 - 1, z2 - 1,
    by simp [squareCorners], by simp [squareCorners], by simp [squareCorners], by simp [squareCorners],
    ?_, ?_, ?_, ?_, ?_, hS, ?_, ?_, ?_, hR0, hR1, hR2⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals first
    | (intro h; simp only [Prod.mk.injEq] at h; omega)
    | (simp only [Edge, incomingNeg, incomingPos, EvenSite]; split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega)

/-- The free table's content: for the free root `z = (z1, z2)`, one of the seven shapes holds with its chain in `S`. -/
def TableShape (R : Site → Site → Prop) (S : Set Site) (z : Site) : Prop :=
  ∃ z1 z2 : ℤ, z = (z1, z2) ∧
    (((z1 + z2) % 2 = 1 ∧ ((z1, z2 + 1) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1 + 1, z2) ∈ S) ∧ R (z1, z2 + 1) (z1 + 1, z2 + 1) ∧ R (z1 + 1, z2 + 1) (z1 + 1, z2) ∧ R (z1 + 1, z2) (z1, z2))
     ∨ ((z1 + z2) % 2 = 0 ∧ ((z1 + 1, z2) ∈ S ∧ (z1 + 1, z2 + 1) ∈ S ∧ (z1, z2 + 1) ∈ S) ∧ R (z1 + 1, z2) (z1 + 1, z2 + 1) ∧ R (z1 + 1, z2 + 1) (z1, z2 + 1) ∧ R (z1, z2 + 1) (z1, z2))
     ∨ ((z1 + z2) % 2 = 0 ∧ ((z1 + 1, z2) ∈ S ∧ (z1 + 1, z2 - 1) ∈ S ∧ (z1, z2 - 1) ∈ S) ∧ R (z1 + 1, z2) (z1 + 1, z2 - 1) ∧ R (z1 + 1, z2 - 1) (z1, z2 - 1) ∧ R (z1, z2 - 1) (z1, z2))
     ∨ ((z1 + z2) % 2 = 1 ∧ ((z1, z2 - 1) ∈ S ∧ (z1 + 1, z2 - 1) ∈ S ∧ (z1 + 1, z2) ∈ S) ∧ R (z1, z2 - 1) (z1 + 1, z2 - 1) ∧ R (z1 + 1, z2 - 1) (z1 + 1, z2) ∧ R (z1 + 1, z2) (z1, z2))
     ∨ ((z1 + z2) % 2 = 0 ∧ ((z1 - 1, z2) ∈ S ∧ (z1 - 1, z2 + 1) ∈ S ∧ (z1, z2 + 1) ∈ S) ∧ R (z1 - 1, z2) (z1 - 1, z2 + 1) ∧ R (z1 - 1, z2 + 1) (z1, z2 + 1) ∧ R (z1, z2 + 1) (z1, z2))
     ∨ ((z1 + z2) % 2 = 1 ∧ ((z1, z2 + 1) ∈ S ∧ (z1 - 1, z2 + 1) ∈ S ∧ (z1 - 1, z2) ∈ S) ∧ R (z1, z2 + 1) (z1 - 1, z2 + 1) ∧ R (z1 - 1, z2 + 1) (z1 - 1, z2) ∧ R (z1 - 1, z2) (z1, z2))
     ∨ ((z1 + z2) % 2 = 1 ∧ ((z1, z2 - 1) ∈ S ∧ (z1 - 1, z2 - 1) ∈ S ∧ (z1 - 1, z2) ∈ S) ∧ R (z1, z2 - 1) (z1 - 1, z2 - 1) ∧ R (z1 - 1, z2 - 1) (z1 - 1, z2) ∧ R (z1 - 1, z2) (z1, z2)))

theorem rowSq_of_tableShape {R : Site → Site → Prop} {S : Set Site} {z : Site} (h : TableShape R S z) :
    RowSq R S z := by
  obtain ⟨z1, z2, rfl, h⟩ := h
  rcases h with ⟨hz, hS, hR0, hR1, hR2⟩ | ⟨hz, hS, hR0, hR1, hR2⟩ | ⟨hz, hS, hR0, hR1, hR2⟩ | ⟨hz, hS, hR0, hR1, hR2⟩ |
    ⟨hz, hS, hR0, hR1, hR2⟩ | ⟨hz, hS, hR0, hR1, hR2⟩ | ⟨hz, hS, hR0, hR1, hR2⟩
  · exact rowSq_S1 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S2 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S3 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S4 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S5 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S6 S z1 z2 hz hS hR0 hR1 hR2
  · exact rowSq_S7 S z1 z2 hz hS hR0 hR1 hR2

/-- **The free parent roots' `ParentSquareOut` from the table** (task 95): a free white root `z ∈ S` (with the rank bound `B` on `S`) has a
forced edge (`free_forced_of_descent`), so its parent square with output holds (`parentSquareOut_of_forced`). -/
theorem parentSquareOut_of_table {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked frame G seed) (hs : seed = fun _ _ => False)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (S : Set Site) (B : ℤ) (hB : ∀ x ∈ S, P.rank x ≤ B)
    (hTab : ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → TableShape P.retained S z)
    {z : Site} (hz : z ∈ S) (hnf : ¬ Nonfree frame z) (hw : laplacian G z = 0) :
    ParentSquareOut G P.retained z := by
  obtain ⟨o, -, hF⟩ := FLatticePaper.W1FreeDescent.free_forced_of_descent P hP hW1 S B hB
    (fun z' hz' hnf' hw' => rowSq_of_tableShape (hTab z' hz' hnf' hw')) z hz hnf hw
  subst hs
  exact parentSquareOut_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF

open FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1NonfreeHsqNonneg

/-- The parent points of the sheet's nonnegative `M`-white sites: the set on which the table and the rank bound are stated. -/
def sheetParentSet (word : Word) : Set Site :=
  {z | ∃ c : Site, 0 ≤ sheetPsi word c ∧ laplacian (MW word) c = 0 ∧ z = zTurn (c - (frameAt word).sheetShift)}

/-- **The lead's `hfree` from the table** (task 95): at the sheet's nonnegative `M`-white sites with nonfree-free parents, the parent square
with output holds. -/
theorem hfree_sheet {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word))
      (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (B : ℤ) (hB : ∀ x ∈ sheetParentSet word, P.rank x ≤ B)
    (hTab : ∀ z ∈ sheetParentSet word, ¬ Nonfree (frameAt (conjWord word)) z →
      laplacian (standardField (conjWord word)) z = 0 → TableShape P.retained (sheetParentSet word) z) :
    ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) := by
  intro c h0 hM hnf
  exact parentSquareOut_of_table P hs hSE.packet hW1 (sheetParentSet word) B hB hTab ⟨c, h0, hM, rfl⟩ hnf
    (FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE h0 hM)

/-- **W1Forced of the sheet minimum from the table, the rank bound and the collar input** (task 95). -/
theorem W1Forced_of_tables {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word))
      (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (B : ℤ) (hB : ∀ x ∈ sheetParentSet word, P.rank x ≤ B)
    (hTab : ∀ z ∈ sheetParentSet word, ¬ Nonfree (frameAt (conjWord word)) z →
      laplacian (standardField (conjWord word)) z = 0 → TableShape P.retained (sheetParentSet word) z)
    (hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
      HsqAt word P c) :
    FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) :=
  FLatticePaper.W1NonfreeHsqC.W1Forced_of_inputs hw hSE P hs hW1 hn3
    (hfree_sheet hw hSE P hs hW1 B hB hTab) hcollar

end FLatticePaper.W1FreeHfree
