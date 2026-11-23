import FLatticePaper.Plane.Induction.FreeSchedule
import FLatticePaper.Plane.Induction.FanTerminal
import FLatticePaper.Plane.Induction.ContactCone

/-! # The full free rows of the schedule (task 108): the minus row and the plus row, and the per-entry trichotomy

The free sites of one deck period are labelled by `V j` (the free V cut `V_j`) and `H j` (the free H trace `H_j`), with `V_{j+L} = V_j + V`
and `H_{j+d} = H_j + U` (Q13's insertion). The two rows of Q1 l.21–30, with the H entries of Q13's insertion (`H_{j+d} = H_j + U`):

* minus: `V_r, …, V_1, H_0, V_0, H_{-1}, …, H_{1-d}, V_{-1}, …, V_{r+1-L}` (`r = D+N`, `L = d+n`);
* plus:  `V_{-r-1}, …, V_{-1}, H_0, V_0, V_1, …, V_{L-r-2}, H_{-1}, …, H_{1-d}` (`H_{d-1}-U, …, H_1-U`).

Each row has `L + d` entries, one for each free label of a deck period.

The removal (Q1 l.30, the trichotomy): if the entry `e` at position `k` lies in the fort, then either a site of the fort has `(P, J)`
componentwise lower with one strict inequality (contradicting the minimum of `K = P + J` over the fort), or an earlier entry of the row
lies in the fort (contradicting the induction), or a fan start `v₀` in the open rectangle touches its own parabola `parabolaField v₀.2`;
`fan_terminal_contradiction` then applies, its paid hypothesis being the earlier entries only.

Named inputs of the row lemma: the minimum of `K` at each entry, the cap window of each touching start, the trichotomy at each entry (the
membership claim, from the forcing of the passage), and the paid set (the boundary touching points on a start's parabola are earlier entries). -/

namespace FLatticePaper.FreeRows

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeSchedule
open FLatticePaper.FanTerminal FLatticePaper.ContactCone

/-- The labels of the free sites of one deck period: the V cut `V_j` and the H trace `H_j`. -/
inductive FreeLabel : Type
  | V : ℤ → FreeLabel
  | H : ℤ → FreeLabel
  deriving DecidableEq

/-- The site of a label, given the enumerations `vAt`, `hAt` of the free V cut and the free H trace. -/
def labelSite (vAt hAt : ℤ → Site) : FreeLabel → Site
  | .V j => vAt j
  | .H j => hAt j

/-- **The minus row** (Q13's insertion): `V_r, …, V_1, H_0, V_0, H_{-1}, …, H_{1-d}, V_{-1}, …, V_{r+1-L}`. -/
def minusRow (r L d : ℤ) : List FreeLabel :=
  ((List.range r.toNat).map fun i : ℕ => FreeLabel.V (r - (i : ℤ))) ++ [FreeLabel.H 0, FreeLabel.V 0] ++
    ((List.range (d - 1).toNat).map fun i : ℕ => FreeLabel.H (-1 - (i : ℤ))) ++
    ((List.range (L - r - 1).toNat).map fun i : ℕ => FreeLabel.V (-1 - (i : ℤ)))

/-- **The plus row** (Q1 l.21–30): `V_{-r-1}, …, V_{-1}, H_0, V_0, V_1, …, V_{L-r-2}, H_{-1}, …, H_{1-d}`. -/
def plusRow (r L d : ℤ) : List FreeLabel :=
  ((List.range (r + 1).toNat).map fun i : ℕ => FreeLabel.V (-r - 1 + (i : ℤ))) ++ [FreeLabel.H 0, FreeLabel.V 0] ++
    ((List.range (L - r - 2).toNat).map fun i : ℕ => FreeLabel.V (1 + (i : ℤ))) ++
    ((List.range (d - 1).toNat).map fun i : ℕ => FreeLabel.H (-1 - (i : ℤ)))

/-- The minus row at `r = 2`, `L = 6`, `d = 3` (so `n = 3`): `V_2, V_1, H_0, V_0, H_{-1}, H_{-2}, V_{-1}, V_{-2}, V_{-3}`. -/
example : minusRow 2 6 3 = [.V 2, .V 1, .H 0, .V 0, .H (-1), .H (-2), .V (-1), .V (-2), .V (-3)] := by decide

/-- The plus row at the same values: `V_{-3}, V_{-2}, V_{-1}, H_0, V_0, V_1, V_2, H_{-1}, H_{-2}`. -/
example : plusRow 2 6 3 = [.V (-3), .V (-2), .V (-1), .H 0, .V 0, .V 1, .V 2, .H (-1), .H (-2)] := by decide

/-- The sites of a row. -/
def rowSites (vAt hAt : ℤ → Site) (row : List FreeLabel) : List Site :=
  row.map (labelSite vAt hAt)

/-- The length of the minus row: `r + 2 + (d−1) + (L−r−1)`, which is `L + d` when `0 ≤ r ≤ L − 1` and `d ≥ 1`. -/
theorem minusRow_length (r L d : ℤ) :
    (minusRow r L d).length = r.toNat + 2 + (d - 1).toNat + (L - r - 1).toNat := by
  simp only [minusRow, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]

/-- The length of the plus row: `(r+1) + 2 + (L−r−2) + (d−1)`. -/
theorem plusRow_length (r L d : ℤ) :
    (plusRow r L d).length = (r + 1).toNat + 2 + (L - r - 2).toNat + (d - 1).toNat := by
  simp only [plusRow, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]

/-- **Ordered removal over a list.** If each entry at a position `k` that lies in `S` forces an earlier entry in `S` (or is excluded by its
own step), no entry of the row lies in `S`. -/
theorem ordered_removal_list (S : Set Site) (row : List Site)
    (hstep : ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∈ S →
      (∀ (j : ℕ) (e' : Site), j < k → row[j]? = some e' → e' ∉ S) → False) :
    ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∉ S := by
  have key : ∀ k : ℕ, ∀ e : Site, row[k]? = some e → e ∉ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro e he hmem
      exact hstep k e he hmem (fun j e' hj hje' => ih j hj e' hje')
  exact key

/-- **The per-entry trichotomy removes a row.** Let `K = P + J` be the potential of the fixed pair, and let `F` be the field with fort `S`.
For the entry `e` at position `k` (`row[k]? = some e`):
* `hmin`: `e` is a minimum of `K` over `S` (the fixed pair);
* `hforce`: if `e ∈ S`, then a fort site has `(P, J)` componentwise lower with one strict inequality, or an earlier entry lies in `S`, or a
  fan start `v₀ ∈ S` in the open rectangle touches its own parabola `parabolaField v₀.2` (the level of the cap `m(k) = −k(k−1)/2` in the
  coordinate `k = y − b_y`, with `b` the start: ALL_SLOPE_STEP's uniform quadratic cap, not the rounded level `J`);
* `hwin`: for each touching interior start, its parabola lies below `F` on the closed polygon (the cap window of the start; named);
* `hpaid`: for such a start, a boundary touching point of `S` on the same parabola is an earlier entry of the row.
Then no entry of the row lies in `S`. -/
theorem free_row_empty (F : Field) (frame : ChildFrame) {S : Set Site} (hfort : IsIncomingFort F S)
    (P J K : Site → ℤ) (hK : ∀ z, K z = P z + J z)
    (row : List Site)
    (hmin : ∀ (k : ℕ) (e : Site), row[k]? = some e → ∀ w ∈ S, K e ≤ K w)
    (hwin : ∀ v0 ∈ S, frame.openRect v0 → F v0 = parabolaField v0.2 v0 →
      ∀ i ∈ frame.closedPolygon, parabolaField v0.2 i ≤ F i)
    (hpaid : ∀ (k : ℕ) (e : Site), row[k]? = some e → ∀ v0 ∈ S, frame.openRect v0 → F v0 = parabolaField v0.2 v0 →
      ∀ w ∈ frame.closedPolygon, ¬ frame.openRect w → w ∈ S → F w = parabolaField v0.2 w →
      ∃ j, j < k ∧ row[j]? = some w)
    (hforce : ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∈ S →
      (∃ w ∈ S, P w ≤ P e ∧ J w ≤ J e ∧ (P w < P e ∨ J w < J e)) ∨
      (∃ j, j < k ∧ ∃ e', row[j]? = some e' ∧ e' ∈ S) ∨
      (∃ v0 ∈ S, frame.openRect v0 ∧ F v0 = parabolaField v0.2 v0)) :
    ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∉ S := by
  refine ordered_removal_list S row ?_
  intro k e he hmem hIH
  rcases hforce k e he hmem with ⟨w, hwS, hwP, hwJ, hwlt⟩ | ⟨j, hj, e', he', he'S⟩ | ⟨v0, hv0S, hv0o, hv0c⟩
  · -- a componentwise lower site of the fort contradicts the minimum of `K`
    have h1 := hmin k e he w hwS
    have h2 := hK e
    have h3 := hK w
    omega
  · exact hIH j e' hj he' he'S
  · -- the fan from the interior start ends on a boundary touching point of the fort, which is an earlier entry (contradicting `hIH`)
    exact fan_terminal_contradiction frame hfort (parabola_binary v0.2) (parabola_lap_even v0.2)
      (hwin v0 hv0S hv0o hv0c) v0 hv0S hv0c hv0o (fun w hwE hwo hwS hwc => by
        obtain ⟨j, hj, hjw⟩ := hpaid k e he v0 hv0S hv0o hv0c w hwE hwo hwS hwc
        exact hIH j w hj hjw hwS)

end FLatticePaper.FreeRows
