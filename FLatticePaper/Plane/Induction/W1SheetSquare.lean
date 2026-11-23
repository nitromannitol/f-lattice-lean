import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1HagreeNonfree

/-! # Task 86: the square data of the sheets from the parent squares (the lead's (1))

The sheet map `c ↦ zTurn (c − lv)` (with `lv` even) carries unit squares to unit squares and inputs to inputs (`zTurn_neighbors`), and its
inverse is `zTurnInv`. So the sheet square data `hsq` of `a_arrow_forced`, for the relation `sheetQ Q lv`, is the parent square data at the
parent point `zTurn (c − lv)`:

`ParentSquare Q z`: a unit square `Q ∋ z` with corners `q₀, q₁, q₂` (the other corners), `q₀` an input of `z` with `¬ Q z q₀` (the rejected
input), and the return chain `q₀ → q₁ → q₂ → z` (each step an edge of the graph and a retained pair of `Q`).

`sheet_square_of_parent`: `ParentSquare Q (zTurn (c − lv))` gives the sheet square data at `c`, for `sheetQ Q lv`. -/

namespace FLatticePaper.W1SheetSquare

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1MSheet FLatticePaper.W1Phase

theorem zTurn_eq_iff (a b : Site) : zTurn a = zTurn b ↔ a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [zTurn, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor <;> omega

/-- The square correspondence: a point of the sheet square with corners `(l₁ + b + 1, l₂ − a − 1)` maps to the parent square `(a, b)`. -/
theorem mem_square_parent (lv p : Site) (a b : ℤ) :
    p ∈ squareCorners (lv.1 + b + 1) (lv.2 - a - 1) ↔ zTurn (p - lv) ∈ squareCorners a b := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨l1, l2⟩ := lv
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, zTurn, Prod.mk_sub_mk]
  constructor <;> intro h <;> omega

/-- The input correspondence: with `lv` even, `y` is an input of `x` exactly when the parent image of `y` is an input of the parent image
of `x`. -/
theorem input_zTurn_iff (lv x y : Site) (hlv : EvenSite lv) :
    (y = incomingNeg x ∨ y = incomingPos x) ↔
      (zTurn (y - lv) = incomingNeg (zTurn (x - lv)) ∨ zTurn (y - lv) = incomingPos (zTurn (x - lv))) := by
  have hn := FLatticePaper.W1HagreeNonfree.zTurn_neighbors x lv hlv
  have hset : (zTurn (y - lv) = incomingNeg (zTurn (x - lv)) ∨ zTurn (y - lv) = incomingPos (zTurn (x - lv))) ↔
      (zTurn (y - lv) = zTurn (incomingNeg x - lv) ∨ zTurn (y - lv) = zTurn (incomingPos x - lv)) := by
    by_cases hx : EvenSite x
    · rw [(hn.1 hx).1, (hn.1 hx).2]
    · rw [(hn.2 hx).1, (hn.2 hx).2]
      exact or_comm
  rw [hset]
  simp only [zTurn_eq_iff, sub_left_inj]

theorem edge_zTurn_iff (lv x y : Site) (hlv : EvenSite lv) :
    Edge y x ↔ Edge (zTurn (y - lv)) (zTurn (x - lv)) :=
  input_zTurn_iff lv x y hlv

/-- The parent square data at a parent point `z`: a unit square through `z`, its other corners `q₀, q₁, q₂` with `q₀` the rejected input
(not retained), and the return chain `q₀ → q₁ → q₂ → z`. -/
def ParentSquare (Q : Site → Site → Prop) (z : Site) : Prop :=
  ∃ q0 q1 q2 : Site, ∃ a b : ℤ,
    z ∈ squareCorners a b ∧ q0 ∈ squareCorners a b ∧ q1 ∈ squareCorners a b ∧ q2 ∈ squareCorners a b ∧
    (∀ c' ∈ squareCorners a b, c' ≠ z → c' = q0 ∨ c' = q1 ∨ c' = q2) ∧
    q0 ≠ q1 ∧ q1 ≠ q2 ∧ q0 ≠ q2 ∧ (q0 = incomingNeg z ∨ q0 = incomingPos z) ∧ ¬ Q z q0 ∧
    Edge q1 q0 ∧ Edge q2 q1 ∧ Edge z q2 ∧ Q q0 q1 ∧ Q q1 q2 ∧ Q q2 z

/-- **The sheet square data from the parent square data** (task 86): for an even sheet shift `lv`, the parent square at `zTurn (c − lv)` gives
the square data of `a_arrow_forced` at `c`, for the relation `sheetQ Q lv`. -/
theorem sheet_square_of_parent {Q : Site → Site → Prop} {lv : Site} (hlv : EvenSite lv) (c : Site)
    (h : ParentSquare Q (zTurn (c - lv))) :
    ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
      ¬ sheetQ Q lv c p0 ∧ Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
      sheetQ Q lv p0 p1 ∧ sheetQ Q lv p1 p2 ∧ sheetQ Q lv p2 c := by
  obtain ⟨q0, q1, q2, a, b, hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3,
    hR0, hR1, hR2⟩ := h
  have hp : ∀ q : Site, zTurn (lv + zTurnInv q - lv) = q := fun q => by
    rw [add_sub_cancel_left, zTurn_zTurnInv]
  refine ⟨lv + zTurnInv q0, lv + zTurnInv q1, lv + zTurnInv q2, lv.1 + b + 1, lv.2 - a - 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_square_parent lv c a b).2 hz
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq0)
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq1)
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq2)
  · intro c' hc' hne
    have h' := (mem_square_parent lv c' a b).1 hc'
    have hne' : zTurn (c' - lv) ≠ zTurn (c - lv) := fun e => hne (sub_left_inj.mp ((zTurn_eq_iff _ _).1 e))
    rcases hcov (zTurn (c' - lv)) h' hne' with e | e | e
    · left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; right
      rw [← e, zTurnInv_zTurn]
      abel
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q1) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne01 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q1) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne12 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne02 h2
  · exact (input_zTurn_iff lv c _ hlv).2 (by rw [hp]; exact hin)
  · unfold sheetQ
    rw [hp]
    exact hrej
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE1)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE2)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp]; exact hE3)
  · unfold sheetQ
    rw [hp, hp]
    exact hR0
  · unfold sheetQ
    rw [hp, hp]
    exact hR1
  · unfold sheetQ
    rw [hp]
    exact hR2

/-- **hsq from the parent squares** (task 86): the square data `hsq` of `a_arrow_forced` for `sheetQ Q`, at every M-white tie, follows from
the parent square data at the parent points `zTurn (c − lv)`. The parent data is the free-root table (the rows of `W1FreeSquare`, with the
rejected input not retained) and the nonfree private squares; both are inputs here. -/
theorem hsq_of_parent {Q : Site → Site → Prop} {lv : Site} (hlv : EvenSite lv)
    (hpar : ∀ c : Site, ParentSquare Q (zTurn (c - lv))) :
    ∀ c : Site,
      ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
        p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
        ¬ sheetQ Q lv c p0 ∧ Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
        sheetQ Q lv p0 p1 ∧ sheetQ Q lv p1 p2 ∧ sheetQ Q lv p2 c :=
  fun c => sheet_square_of_parent hlv c (hpar c)

end FLatticePaper.W1SheetSquare
