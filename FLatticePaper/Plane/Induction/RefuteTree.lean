import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.AuxRankQ1

/-! # Refutation trees: the soundness of the forced-branch rules, and the ordered row removal

For a field `F`, a sign `η = ±1`, a set `E` of earlier row entries and a set `C` of core sites, `Refuted E C x` is the least predicate
closed under the four rules of the forced branches of a restricted fort for `permitsQ1 frame F η` (Q1 l.21–30):

* `earlier`: `x ∈ E` (an earlier entry of the displayed row, whose non-membership is the induction hypothesis);
* `core`: `x ∈ C` (the open rectangle, excluded by the core argument);
* `lowPair`: `P x ≤ c₀`, `J x ≤ 0`, `(P x, J x) ≠ (c₀, 0)` (componentwise below the minimal pair, so `K x < c₀`);
* `white`: `laplacian F x = 0` and some input `i` permitted by `permitsQ1` is refuted (a free white keeps its prescribed input, a
  nonfree white keeps both: one refuted input refutes `x`);
* `black`: `laplacian F x = −1` and both inputs are refuted (a black site keeps both inputs, one of which must lie in the fort).

`refuted_not_mem`: a refuted site is not in a restricted fort whose sites have `K ≥ c₀` (the minimum), given `E` and `C` are outside it.
`row_removed_of_refuted`: if every entry of a row has a refutation whose earlier entries are the entries before it, no entry is in the
fort. The named inputs of a family are exactly the refutation trees of its entries (numerically verified, see `route_memo`/`lfp` in the
scratch notes); this file proves the soundness, not the trees. -/

namespace FLatticePaper.RefuteTree

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1

/-- The refuted sites. -/
inductive Refuted (frame : ChildFrame) (F : Field) (η : ℤ) (E C : Site → Prop) : Site → Prop
  | earlier {x : Site} : E x → Refuted frame F η E C x
  | core {x : Site} : C x → Refuted frame F η E C x
  | lowPair {x : Site} :
      frame.price F x ≤ frame.cutPrice → frame.roundedSlip F η x ≤ 0 →
        (frame.price F x ≠ frame.cutPrice ∨ frame.roundedSlip F η x ≠ 0) → Refuted frame F η E C x
  | white {x i : Site} : laplacian F x = 0 → permitsQ1 frame F η x i →
      Refuted frame F η E C i → Refuted frame F η E C x
  | black {x : Site} : laplacian F x = -1 →
      Refuted frame F η E C (incomingNeg x) → Refuted frame F η E C (incomingPos x) → Refuted frame F η E C x

/-- A permitted input of `permitsQ1` is an input of the site (`η = ±1`). -/
theorem permitsQ1_edge (frame : ChildFrame) (F : Field) {η : ℤ} (hη : η = 1 ∨ η = -1) {x i : Site}
    (h : permitsQ1 frame F η x i) : i = incomingNeg x ∨ i = incomingPos x := by
  rcases h with ⟨-, he⟩ | ⟨-, hc⟩
  · exact he
  · rcases hc with ⟨-, hp⟩ | ⟨-, he⟩
    · exact FLatticePaper.FreePolicy.freePresc_input frame η hη hp
    · exact he

/-- **Soundness of the refutation rules.** In a restricted fort `S` for `permitsQ1 frame F η` whose sites have `K ≥ c₀`
(`K = P + J_η`), a refuted site is not in `S`, provided the earlier entries and the core sites are not in `S`. -/
theorem refuted_not_mem (frame : ChildFrame) (F : Field) {η : ℤ} (hη : η = 1 ∨ η = -1) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z)
    {E C : Site → Prop} (hE : ∀ x, E x → x ∉ S) (hC : ∀ x, C x → x ∉ S) :
    ∀ x, Refuted frame F η E C x → x ∉ S := by
  intro x hx
  induction hx with
  | @earlier y h => exact hE y h
  | @core y h => exact hC y h
  | @lowPair y hp hJ hne =>
    intro hyS
    have hk := hK y hyS
    rcases hne with hne | hne <;> omega
  | @white y i hw hpi hri ih =>
    intro hyS
    have hi : i ∈ S := by
      rcases hres y hyS with ⟨hl, -⟩ | ⟨-, hn, hp⟩
      · rw [hl] at hw
        norm_num at hw
      · rcases permitsQ1_edge frame F hη hpi with rfl | rfl
        · exact hn.resolve_right (fun h => h hpi)
        · exact hp.resolve_right (fun h => h hpi)
    exact ih hi
  | @black y hl hneg hpos ihn ihp =>
    intro hyS
    have hPn : permitsQ1 frame F η y (incomingNeg y) := Or.inl ⟨hl, Or.inl rfl⟩
    have hPp : permitsQ1 frame F η y (incomingPos y) := Or.inl ⟨hl, Or.inr rfl⟩
    rcases hres y hyS with ⟨-, hsome⟩ | ⟨hw, -⟩
    · rcases hsome with (h | h) | (h | h)
      · exact ihn h
      · exact absurd hPn h
      · exact ihp h
      · exact absurd hPp h
    · rw [hl] at hw
      norm_num at hw

/-- **The ordered row removal by refutation.** If every entry `row[k]` has a refutation whose earlier entries are the entries before
`k`, and the core sites are outside the fort, then no entry of the row is in the fort. -/
theorem row_removed_of_refuted (frame : ChildFrame) (F : Field) {η : ℤ} (hη : η = 1 ∨ η = -1) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z)
    {C : Site → Prop} (hC : ∀ x, C x → x ∉ S) (row : List Site)
    (href : ∀ (k : ℕ) (e : Site), row[k]? = some e →
      Refuted frame F η (fun x => ∃ j : ℕ, j < k ∧ row[j]? = some x) C e) :
    ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∉ S := by
  refine FreeRows.ordered_removal_list S row ?_
  intro k e he hmem hIH
  have hE : ∀ x, (∃ j : ℕ, j < k ∧ row[j]? = some x) → x ∉ S := by
    rintro x ⟨j, hj, hjx⟩
    exact hIH j x hj hjx
  exact refuted_not_mem frame F hη hres hK hE hC e (href k e he) hmem

end FLatticePaper.RefuteTree
