import FLatticePaper.Plane.Induction.H0CoreRecurrent
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.SheetFort

/-! # The `H₀` core for restricted forts of `permitsQ1` (minus sign), from recurrence

Let `S` be a restricted fort of `permitsQ1 frame F (−1)` (the auxiliary game of Q1), and `M` a recurrent field with `F = M` on the closed
polygon. The steps (the restricted analogue of `H0CoreRecurrent.h0_core_minus_recurrent`):

1. An open site of `S` is nonfree (`StrictNonfree`), so both of its inputs are permitted; its restricted condition is then the
   incoming-fort condition, and its inputs lie in the closed polygon. Its inputs that are in `S` are open (by the candidate
   hypothesis and `minus_not_called`). So `S ∩ openRect` is an incoming fort of `M`, which is empty by recurrence.
2. At a site `c ∈ S` whose south input `incomingNeg c` is outside `S`, the restricted condition forces `incomingPos c ∈ S`
   (`restricted_forced_pos`): a black site keeps both inputs, a white site with `freeClosure` has exactly one prescribed input.
3. `H₀ = (1, 0)` and `V₀ = (0, 0)`: their south and west inputs `(1, −1)` and `(−1, 0)` lie outside the closed polygon. If these
   two inputs are not in `S` (the named hypotheses `hout1`, `hout2`), step 2 forces `(1, 1)` (open) into `S` and `H₀` into `S`.

So the conclusion `∀ z ∈ S, z ∉ closedPolygon` holds from the two named facts `(1,−1) ∉ S` and `(−1,0) ∉ S`. -/

namespace FLatticePaper.RestrictedH0Core

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.H0Core FLatticePaper.FreeClosure
open FLatticePaper.FreePolicy

/-- An open rectangle site lies in the closed polygon (the strict inequalities of `openRect` give the closed ones). -/
theorem openRect_mem_closed (frame : ChildFrame) {z : Site} (hz : frame.openRect z) : z ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  unfold ChildFrame.openRect at hz
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  split_ifs at hz ⊢ <;> omega

/-- An open rectangle site is not free: it is not in the deck closure of the free H and V cuts. -/
theorem openRect_not_freeClosure (frame : ChildFrame) {c : Site} (hc : frame.openRect c) : ¬ freeClosure frame c := by
  intro hcl
  obtain ⟨s, hs, h⟩ := hcl
  exact FLatticePaper.Induction.strictInterior_nonfree frame ((FLatticePaper.W1Exit.openRect_iff frame c).1 hc) s hs
    ((Set.mem_union _ _ _).2 h)

/-- **Forced input.** If `incomingNeg c ∉ S` and `c ∈ S`, the restricted condition gives `incomingPos c ∈ S`. -/
theorem restricted_forced_pos {F : Field} (frame : ChildFrame) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F (-1)) S) {c : Site} (hc : c ∈ S) (hneg : incomingNeg c ∉ S) :
    incomingPos c ∈ S := by
  rcases hres c hc with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · -- black: both inputs are permitted, so the other input is in `S`
    have hPn : permitsQ1 frame F (-1) c (incomingNeg c) := Or.inl ⟨hl, Or.inl rfl⟩
    have hPp : permitsQ1 frame F (-1) c (incomingPos c) := Or.inl ⟨hl, Or.inr rfl⟩
    rcases hsome with (h | h) | (h | h)
    · exact absurd h hneg
    · exact absurd hPn h
    · exact h
    · exact absurd hPp h
  · -- white: `freeClosure c` (else the south input is permitted by the edge clause), and the prescribed input is the north one
    have hPneg : ¬ permitsQ1 frame F (-1) c (incomingNeg c) := hn.resolve_left hneg
    have hfc : freeClosure frame c := by
      by_contra hfc
      exact hPneg (Or.inr ⟨hl, Or.inr ⟨hfc, Or.inl rfl⟩⟩)
    obtain ⟨i, hi⟩ := freePresc_exists frame (-1) hfc
    have hEi := freePresc_input frame (-1) (Or.inr rfl) hi
    have hipos : i = incomingPos c := by
      unfold Edge at hEi
      rcases hEi with h | h
      · exfalso
        exact hPneg (Or.inr ⟨hl, Or.inl ⟨hfc, by rw [← h]; exact hi⟩⟩)
      · exact h
    have hPpos : permitsQ1 frame F (-1) c (incomingPos c) :=
      Or.inr ⟨hl, Or.inl ⟨hfc, by rw [← hipos]; exact hi⟩⟩
    rcases hp with h | h
    · exact h
    · exact absurd hPpos h

/-- **The interior of a restricted fort is empty** (recurrence of `M`). The candidate hypothesis places the boundary points of `S`
outside the open rectangle at `H₀` and `V₀`. -/
theorem interior_empty_restricted {F M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    (hM : ∀ s ∈ frame.closedPolygon, F s = M s) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z →
      z = FLatticePaper.Induction.hFirst ∨ z = FLatticePaper.Induction.vFirst) :
    ∀ z ∈ S, ¬ frame.openRect z := by
  have hT : IsIncomingFort M {y | y ∈ S ∧ frame.openRect y} := by
    intro x hx
    have hxS : x ∈ S := hx.1
    have hxo : frame.openRect x := hx.2
    have hlap : laplacian F x = laplacian M x := by
      unfold laplacian
      rw [hM x (openRect_mem_closed frame hxo),
        hM _ (FLatticePaper.W1Exit.rectInputs frame x hxo _ (Or.inl rfl)),
        hM _ (FLatticePaper.W1Exit.rectInputs frame x hxo _ (Or.inr rfl))]
    have inner : ∀ i, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ S → frame.openRect i := by
      intro i hi hiS
      by_contra hnot
      rcases hcand i hiS (FLatticePaper.W1Exit.rectInputs frame x hxo i hi) hnot with h | h
      · exact minus_not_called frame x hxo i (Or.inl h) hi
      · exact minus_not_called frame x hxo i (Or.inr h) hi
    rcases hres x hxS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
    · -- black: a black open site keeps both inputs, so one of them is in `S`
      have hl' : laplacian M x = -1 := by rw [← hlap]; exact hl
      have hPn : permitsQ1 frame F (-1) x (incomingNeg x) := Or.inl ⟨hl, Or.inl rfl⟩
      have hPp : permitsQ1 frame F (-1) x (incomingPos x) := Or.inl ⟨hl, Or.inr rfl⟩
      have hsome' : incomingNeg x ∈ S ∨ incomingPos x ∈ S := by
        rcases hsome with (h | h) | (h | h)
        · exact Or.inl h
        · exact absurd hPn h
        · exact Or.inr h
        · exact absurd hPp h
      refine Or.inl ⟨hl', ?_⟩
      rcases hsome' with h | h
      · exact Or.inl ⟨h, inner _ (Or.inl rfl) h⟩
      · exact Or.inr ⟨h, inner _ (Or.inr rfl) h⟩
    · -- white: both inputs are in `S` (the open site is nonfree, so both are permitted)
      have hl' : laplacian M x = 0 := by rw [← hlap]; exact hl
      have hnf := openRect_not_freeClosure frame hxo
      have hPn : permitsQ1 frame F (-1) x (incomingNeg x) := Or.inr ⟨hl, Or.inr ⟨hnf, Or.inl rfl⟩⟩
      have hPp : permitsQ1 frame F (-1) x (incomingPos x) := Or.inr ⟨hl, Or.inr ⟨hnf, Or.inr rfl⟩⟩
      have h1 : incomingNeg x ∈ S := hn.resolve_right (fun h => h hPn)
      have h2 : incomingPos x ∈ S := hp.resolve_right (fun h => h hPp)
      exact Or.inr ⟨hl', ⟨h1, inner _ (Or.inl rfl) h1⟩, ⟨h2, inner _ (Or.inr rfl) h2⟩⟩
  have hfin : {y | y ∈ S ∧ frame.openRect y}.Finite :=
    (FLatticePaper.FanTerminal.openRect_finite frame).subset (fun y hy => hy.2)
  have hempty := FLatticePaper.SheetFort.no_finite_fort_of_recurrent hrec hT hfin
  intro z hz ho
  have hmem : z ∈ {y | y ∈ S ∧ frame.openRect y} := ⟨hz, ho⟩
  rw [hempty] at hmem
  exact hmem

/-- **Forced input of a free white.** If `c` is white, its prescribed input is `incomingPos c` and not `incomingNeg c` (the
`FreePresc` set of a free white is the single prescribed input), then `c ∈ S` forces `incomingPos c ∈ S`. -/
theorem forced_pos_presc {F : Field} (frame : ChildFrame) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F (-1)) S) {c : Site} (hc : c ∈ S)
    (hw : laplacian F c = 0) (hpos : FreePresc frame (-1) c (incomingPos c))
    (hnotneg : ¬ FreePresc frame (-1) c (incomingNeg c)) : incomingPos c ∈ S := by
  have hfc : freeClosure frame c := by
    obtain ⟨t, ht, h⟩ := hpos
    refine ⟨t, ht, ?_⟩
    rcases h with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hres c hc with ⟨hl, -⟩ | ⟨-, -, hp⟩
  · rw [hl] at hw
    norm_num at hw
  · have hPneg : ¬ permitsQ1 frame F (-1) c (incomingNeg c) := by
      intro h
      rcases h with ⟨hl', -⟩ | ⟨-, hc'⟩
      · rw [hw] at hl'
        norm_num at hl'
      · rcases hc' with ⟨-, hP⟩ | ⟨hnf, -⟩
        · exact hnotneg hP
        · exact hnf hfc
    have hPpos : permitsQ1 frame F (-1) c (incomingPos c) := Or.inr ⟨hw, Or.inl ⟨hfc, hpos⟩⟩
    rcases hp with h | h
    · exact h
    · exact absurd hPpos h

/-- **The minus `H₀` core for restricted forts.** The fort `S` (restricted, recurrent comparison field `M = F` on the closed polygon,
boundary candidates `H₀`, `V₀`) lies outside the closed polygon. The two free whites `H₀` and `V₀` have prescribed inputs `(1, 1)`
(interior) and `H₀`, so no outside input is needed (`hout1`, `hout2` are dropped). The hypotheses `hH0w`, `hV0w` (white) and
`hH0p`, `hV0p` (the free prescription is the single input) are the colour and prescription facts checked numerically on the proper
words of length `≤ 4` (minus sign). -/
theorem h0_core_restricted_minus {F M : Field} (frame : ChildFrame) (hrec : FLatticePaper.RecurrentField M)
    (hM : ∀ s ∈ frame.closedPolygon, F s = M s) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z →
      z = FLatticePaper.Induction.hFirst ∨ z = FLatticePaper.Induction.vFirst)
    (hH0w : laplacian F ((1 : ℤ), (0 : ℤ)) = 0) (hV0w : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hH0p : ∀ i, FreePresc frame (-1) ((1 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (1 : ℤ)))
    (hV0p : ∀ i, FreePresc frame (-1) ((0 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (0 : ℤ))) :
    ∀ z ∈ S, z ∉ frame.closedPolygon := by
  have hint := interior_empty_restricted frame hrec hM hres hcand
  have hH0 : ((1 : ℤ), (0 : ℤ)) ∉ S := by
    intro h
    have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hn : incomingNeg ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_not_even _ hodd]
      simp
    have hp : incomingPos ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
      rw [incomingPos_of_not_even _ hodd]
      simp
    have hpos : FreePresc frame (-1) ((1 : ℤ), (0 : ℤ)) (incomingPos ((1 : ℤ), (0 : ℤ))) := by
      rw [hp]
      exact (hH0p _).mpr rfl
    have hnotneg : ¬ FreePresc frame (-1) ((1 : ℤ), (0 : ℤ)) (incomingNeg ((1 : ℤ), (0 : ℤ))) := by
      rw [hn]
      intro hh
      have h' := (hH0p _).mp hh
      norm_num [Prod.ext_iff] at h'
    have h11 : ((1 : ℤ), (1 : ℤ)) ∈ S := by
      have := forced_pos_presc frame hres h hH0w hpos hnotneg
      rw [hp] at this
      exact this
    exact hint _ h11 (open_one_one frame)
  have hV0 : ((0 : ℤ), (0 : ℤ)) ∉ S := by
    intro h
    have hev : EvenSite ((0 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hn : incomingNeg ((0 : ℤ), (0 : ℤ)) = ((-1 : ℤ), (0 : ℤ)) := by
      rw [incomingNeg_of_even _ hev]
      simp
    have hp : incomingPos ((0 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
      rw [incomingPos_of_even _ hev]
      simp
    have hpos : FreePresc frame (-1) ((0 : ℤ), (0 : ℤ)) (incomingPos ((0 : ℤ), (0 : ℤ))) := by
      rw [hp]
      exact (hV0p _).mpr rfl
    have hnotneg : ¬ FreePresc frame (-1) ((0 : ℤ), (0 : ℤ)) (incomingNeg ((0 : ℤ), (0 : ℤ))) := by
      rw [hn]
      intro hh
      have h' := (hV0p _).mp hh
      norm_num [Prod.ext_iff] at h'
    have h10 : ((1 : ℤ), (0 : ℤ)) ∈ S := by
      have := forced_pos_presc frame hres h hV0w hpos hnotneg
      rw [hp] at this
      exact this
    exact hH0 h10
  intro z hz hcl
  by_cases ho : frame.openRect z
  · exact hint z hz ho
  · rcases hcand z hz hcl ho with rfl | rfl
    · exact hH0 hz
    · exact hV0 hz

end FLatticePaper.RestrictedH0Core
