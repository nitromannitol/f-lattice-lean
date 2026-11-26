import FLatticePaper.Plane.Induction.InternalReturns
import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.FreeVCutExist
import FLatticePaper.Plane.Induction.FreeCutExist
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.DeckSelection
import FLatticePaper.Plane.Induction.ChainWire

/-! # The free route assembly: the predecessor split and the deck transport of `ParentSquareOut`

Part 1: the axial predecessor of an odd free H root (the diagonal one is excluded by `tGrade ≠ n`, from `z ≠ hFirst`).
Part 2: `ParentSquareOut` moves by a deck-even translation, given deck equivariance of the policy and periodicity of the Laplacian. -/

namespace FLatticePaper.FreeCutPred

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem freeH_pred_axial_of_odd (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hp : (x + y) % 2 = 1)
    (hne : frame.tGrade (x, y) ≠ frame.child.num) :
    (x - 1, y) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hsb := (ArcFrame.freeH_vertex_bounds frame hnodd hdodd hz).2
    (by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega)
  have hpar : w1t frame.child.num frame.child.den (x, y) % 2 = (x + y) % 2 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    simpa [tGrade_eq_w1t] using h
  have htne : w1t frame.child.num frame.child.den (x, y) ≠ frame.child.num := by
    simpa [tGrade_eq_w1t] using hne
  have o0 : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
  have es : EvenSite (x, y - 1) := by unfold EvenSite; show (x + (y - 1)) % 2 = 0; omega
  have ep1 : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  have op1s : ¬ EvenSite (x - 1, y - 1) := by unfold EvenSite; show ¬ ((x - 1 + (y - 1)) % 2 = 0); omega
  have ep2s : EvenSite (x - 1, y - 1 - 1) := by
    unfold EvenSite; show (x - 1 + (y - 1 - 1)) % 2 = 0; omega
  simp only [sGrade_eq_w1s, frame_periodDenominator_eq] at hsb
  simp only [FreeCutSucc.mem_freeH_iff, closedRect, ChildFrame.hSpectrum, tGrade_eq_w1t,
    if_neg o0, if_pos es, if_pos ep1, if_neg op1s] at hz ⊢
  simp only [w1t_predX, w1s_predX, w1t_predY, w1s_predY] at hz ⊢
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

end FLatticePaper.FreeCutPred

namespace FLatticePaper.FreeRoutes

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeOut FLatticePaper.AndOrRank

theorem mem_squareCorners_add_iff (a b : ℤ) (s c : Site) :
    c + s ∈ squareCorners (a + s.1) (b + s.2) ↔ c ∈ squareCorners a b := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨s1, s2⟩ := s
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> intro h <;> omega

theorem edge_add {s : Site} (hs : EvenSite s) {y x : Site} (h : Edge y x) : Edge (y + s) (x + s) := by
  unfold Edge at h ⊢
  rcases h with h | h
  · left; rw [DeckSelection.incomingNeg_add_even hs x, h]
  · right; rw [DeckSelection.incomingPos_add_even hs x, h]

theorem isInput_add {s : Site} (hs : EvenSite s) {z x : Site} (h : x = incomingNeg z ∨ x = incomingPos z) :
    x + s = incomingNeg (z + s) ∨ x + s = incomingPos (z + s) := by
  rcases h with h | h
  · left; rw [DeckSelection.incomingNeg_add_even hs z, h]
  · right; rw [DeckSelection.incomingPos_add_even hs z, h]

/-- **Transport of the parent-square predicate by a deck-even translation.** If the policy `R` is invariant under the translation
`s` and the Laplacian is `s`-periodic, the witness of `z` moves to a witness of `z + s`. -/
theorem parentSquareOut_add {G : Field} {R : Site → Site → Prop} {s : Site} (hs : EvenSite s)
    (hR : ∀ x u, R x u ↔ R (x + s) (u + s)) (hL : ∀ x, laplacian G (x + s) = laplacian G x)
    {z : Site} (h : ParentSquareOut G R z) : ParentSquareOut G R (z + s) := by
  obtain ⟨q0, q1, q2, o, a, b, hz, hq0c, hq1c, hq2c, hcov, hd1, hd2, hd3, hq0, hq0R, hE1, hE2, hE3,
    hR0, hR1, hR2, ho, hoC, hzo, hzu, hl0, hl1, hl2⟩ := h
  have hcin : ∀ c, c + s ∈ squareCorners (a + s.1) (b + s.2) → c ∈ squareCorners a b :=
    fun c hc => (mem_squareCorners_add_iff a b s c).1 hc
  have hcout : ∀ c, c ∈ squareCorners a b → c + s ∈ squareCorners (a + s.1) (b + s.2) :=
    fun c hc => (mem_squareCorners_add_iff a b s c).2 hc
  have hl0' : laplacian G (q0 + s) = -1 ∨ (laplacian G (q0 + s) = 0 ∧ ∀ j, R (q0 + s) j → j = q1 + s) := by
    rcases hl0 with h | ⟨h0, hu⟩
    · exact Or.inl (by rw [hL q0]; exact h)
    · refine Or.inr ⟨by rw [hL q0]; exact h0, fun j hj => ?_⟩
      have hj' : R q0 (j - s) := (hR q0 (j - s)).2 (by rw [sub_add_cancel]; exact hj)
      have := hu _ hj'
      rw [← this, sub_add_cancel]
  have hl1' : laplacian G (q1 + s) = -1 ∨ (laplacian G (q1 + s) = 0 ∧ ∀ j, R (q1 + s) j → j = q2 + s) := by
    rcases hl1 with h | ⟨h0, hu⟩
    · exact Or.inl (by rw [hL q1]; exact h)
    · refine Or.inr ⟨by rw [hL q1]; exact h0, fun j hj => ?_⟩
      have hj' : R q1 (j - s) := (hR q1 (j - s)).2 (by rw [sub_add_cancel]; exact hj)
      have := hu _ hj'
      rw [← this, sub_add_cancel]
  have hl2' : laplacian G (q2 + s) = -1 ∨ (laplacian G (q2 + s) = 0 ∧ ∀ j, R (q2 + s) j → j = z + s) := by
    rcases hl2 with h | ⟨h0, hu⟩
    · exact Or.inl (by rw [hL q2]; exact h)
    · refine Or.inr ⟨by rw [hL q2]; exact h0, fun j hj => ?_⟩
      have hj' : R q2 (j - s) := (hR q2 (j - s)).2 (by rw [sub_add_cancel]; exact hj)
      have := hu _ hj'
      rw [← this, sub_add_cancel]
  refine ⟨q0 + s, q1 + s, q2 + s, o + s, a + s.1, b + s.2, hcout z hz, hcout q0 hq0c, hcout q1 hq1c,
    hcout q2 hq2c, ?_, fun h => hd1 (add_right_cancel h), fun h => hd2 (add_right_cancel h),
    fun h => hd3 (add_right_cancel h), isInput_add hs hq0, fun h => hq0R ((hR z q0).2 h),
    edge_add hs hE1, edge_add hs hE2, edge_add hs hE3, (hR q0 q1).1 hR0, (hR q1 q2).1 hR1,
    (hR q2 z).1 hR2, isInput_add hs ho, fun h => hoC (hcin o h), (hR z o).1 hzo, ?_, hl0', hl1', hl2'⟩
  · intro c' hc hne
    have hold : c' - s ∈ squareCorners a b := hcin (c' - s) (by rw [sub_add_cancel]; exact hc)
    have hne' : c' - s ≠ z := fun h => hne (by rw [← h, sub_add_cancel])
    rcases hcov (c' - s) hold hne' with h | h | h
    · exact Or.inl (by rw [← sub_add_cancel c' s, h])
    · exact Or.inr (Or.inl (by rw [← sub_add_cancel c' s, h]))
    · exact Or.inr (Or.inr (by rw [← sub_add_cancel c' s, h]))
  · intro j hj
    have h' : R z (j - s) := (hR z (j - s)).2 (by rw [sub_add_cancel]; exact hj)
    have := hzu _ h'
    rw [← this, sub_add_cancel]

end FLatticePaper.FreeRoutes

namespace FLatticePaper.FreeRoutes

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeOut FLatticePaper.AndOrRank FLatticePaper.InternalReturns

/-! ### The genuine route facts (RegionalCompat), per case

Each field is the hypothesis of one case of section C or D, stated for the canonical policy `C` of the sign `η`: the genuine arrows
`q → next` of the route, each as "black, or kept by the policy". The predecessor condition of a case is part of its field. -/
structure RouteGenuine {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η) : Prop where
  h1 : ∀ z ∈ frame.freeH, laplacian G z = 0 → ¬ EvenSite z → z ≠ FLatticePaper.Induction.hFirst → z ≠ frame.hLast →
    (laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) (z.1 - 1, z.2 - 1)) ∧
    (laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1 - 1, z.2)) ∧
    (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z)
  h2 : ∀ z ∈ frame.freeH, laplacian G z = 0 → EvenSite z → (z.1 - 1, z.2 - 1) ∈ frame.freeH →
    (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 - 1)) ∧
    (laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1, z.2 - 1)) ∧
    (laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) z)
  /-- `H_1 = (2,0)` is excluded: its route is the row `rH1` (`C.2` for `η = 1`, `C.3` for `η = -1`), since for `η = 1` the
  arrow `(1,0) → (1,1)` of this field contradicts the row's `(1,0)` keeping `(1,-1)`. -/
  h3 : ∀ z ∈ frame.freeH, z ≠ (2, 0) → laplacian G z = 0 → EvenSite z → (z.1 - 1, z.2) ∈ frame.freeH →
    (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 + 1)) ∧
    (laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ C.policy (z.1 - 1, z.2 + 1) (z.1, z.2 + 1)) ∧
    (laplacian G (z.1, z.2 + 1) = -1 ∨ C.policy (z.1, z.2 + 1) z)
  v2 : ∀ z ∈ frame.freeV, laplacian G z = 0 → ¬ EvenSite z → (z.1 + -η, z.2 - -η) ∈ frame.freeV →
    (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 + -η, z.2 - -η)) ∧
    (laplacian G (z.1 + -η, z.2 - -η) = -1 ∨ C.policy (z.1 + -η, z.2 - -η) (z.1 + -η, z.2)) ∧
    (laplacian G (z.1 + -η, z.2) = -1 ∨ C.policy (z.1 + -η, z.2) z)
  /-- `V_1 = (0,1)` is excluded for `η = -1`: its route is the row `rV1` (the `v2` route), since its axial predecessor
  `(0,0)` and its diagonal `(1,0)` are both free, and the `v3` arrows contradict the row. -/
  v3 : ∀ z ∈ frame.freeV, ¬ (η = -1 ∧ z = (0, 1)) → laplacian G z = 0 → ¬ EvenSite z → (z.1, z.2 - -η) ∈ frame.freeV →
    (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 - -η, z.2 - -η)) ∧
    (laplacian G (z.1 - -η, z.2 - -η) = -1 ∨ C.policy (z.1 - -η, z.2 - -η) (z.1 - -η, z.2)) ∧
    (laplacian G (z.1 - -η, z.2) = -1 ∨ C.policy (z.1 - -η, z.2) z)
  /-- The endpoint rows of section D, for the sign: `η = 1` at `H_0`; `η = -1` at `H_0`. -/
  rH0 : (η = 1 → (laplacian G (0, 1) = -1 ∨ C.policy (0, 1) (0, 0)) ∧ (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0))) ∧
    (η = -1 → (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (0, -1)) ∧ (laplacian G (0, -1) = -1 ∨ C.policy (0, -1) (0, 0)) ∧
      (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0)))
  /-- The row at `H_last`, at the representative `(0,-1) = H_last - U` (transported by the deck translation `U`). -/
  rHlast : (laplacian G (-1, -2) = -1 ∨ C.policy (-1, -2) (-1, -1)) ∧ (laplacian G (-1, -1) = -1 ∨ C.policy (-1, -1) (0, -1))
  /-- The rows at `H_1 = (2,0)`. -/
  rH1 : (η = 1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, -1)) ∧ (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1))) ∧
    (η = -1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, 1)) ∧ (laplacian G (2, 1) = -1 ∨ C.policy (2, 1) (2, 0)))
  /-- The row at `V_1 = (0,1)` for `η = -1`. -/
  rV1 : η = -1 → (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0)) ∧ (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, 1))
  /-- The row at `V_prev`, at the representative `(1,-2)` (transported by `V`), for `η = 1`. -/
  rVprev : η = 1 → (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1)) ∧ (laplacian G (2, -2) = -1 ∨ C.policy (2, -2) (1, -2))

end FLatticePaper.FreeRoutes

namespace FLatticePaper.FreeRoutes

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeOut FLatticePaper.AndOrRank FLatticePaper.InternalReturns

theorem combine_one_zero (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 1 0 = (frame.child.den, frame.child.num) := by
  rw [DeckSelection.combine_eq frame 1 0, StripColours.kernel_eq frame]
  simp

theorem combine_zero_one (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 0 1 = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  rw [DeckSelection.combine_eq frame 0 1, StripColours.transverse_eq frame]
  simp

theorem evenSite_combine_one_zero (frame : ChildFrame) : EvenSite (frame.child.modifiedDeck.combine 1 0) := by
  rw [DeckSelection.combine_eq frame 1 0]; exact DeckSelection.evenSite_span frame 1 0

theorem evenSite_combine_zero_one (frame : ChildFrame) : EvenSite (frame.child.modifiedDeck.combine 0 1) := by
  rw [DeckSelection.combine_eq frame 0 1]; exact DeckSelection.evenSite_span frame 0 1

theorem prescribedH_hLast (frame : ChildFrame) (η : ℤ) : frame.prescribedH η frame.hLast = (0, 1) := by
  have hne : frame.hLast ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 : frame.hLast.1 = FLatticePaper.Induction.hFirst.1 := by rw [h]
    obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
    simp [ChildFrame.hLast, FLatticePaper.Induction.hFirst] at h1
    omega
  unfold ChildFrame.prescribedH
  simp [hne]

/-- The free-cut predecessor for `freeV` at an odd site, in the traversal direction `-η`: one of the two predecessors is free. -/
theorem freeV_split (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site} (hz : z ∈ frame.freeV)
    (hodd : ¬ EvenSite z) :
    (z.1, z.2 - -η) ∈ frame.freeV ∨ (z.1 + -η, z.2 - -η) ∈ frame.freeV := by
  rcases hη with rfl | rfl
  · have hne : z ≠ frame.vLast := by
      intro h; rw [h] at hodd; apply hodd; unfold EvenSite ChildFrame.vLast; simp only; omega
    have := FreeVCutExist.freeV_succ_exists frame hz hne
    simpa [sub_eq_add_neg] using this
  · exact FreeCutPred.freeV_pred_exists frame hz (by
      intro h; rw [h] at hodd; apply hodd; unfold EvenSite FLatticePaper.Induction.vFirst; simp only; omega)

theorem freeH_split (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hne : z ≠ FLatticePaper.Induction.hFirst) :
    (z.1 - 1, z.2) ∈ frame.freeH ∨ (z.1 - 1, z.2 - 1) ∈ frame.freeH :=
  FreeCutPred.freeH_pred_exists frame hz hne

/-- **The horizontal parent-square witnesses for every free H root with zero Laplacian**, from the canonical policy and the
genuine route facts (`RouteGenuine`); `H_0`, `H_last` and `H_1` are the endpoint rows, transported where they sit at a
representative. -/
theorem hH_of_routes {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hη : η = 1 ∨ η = -1) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (Rg : RouteGenuine C) :
    ∀ z ∈ frame.freeH, laplacian G z = 0 → ParentSquareOut G C.policy z := by
  intro z hz hw
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hS : frame.HasStrips G := hP.strips
  have hL : LocalRetention G C.policy := LocalRetention.of_canonical C hbin
  have hPol : ∀ x u, C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine 1 0) (u + frame.child.modifiedDeck.combine 1 0) :=
    fun x u => hdeck 1 0 x u
  have hTr : ∀ x, laplacian G (x + frame.child.modifiedDeck.combine 1 0) = laplacian G x := by
    intro x; rw [combine_one_zero frame]; exact StripColours.lap_add_kernel frame hP.periods x
  by_cases h1 : z = FLatticePaper.Induction.hFirst
  · subst h1
    rcases hη with h | h
    · have hpr : ∀ j, C.policy FLatticePaper.Induction.hFirst j ↔ j = (1, -1) := by
        intro j
        rw [C.prescribed.1 _ hz hw j, ChildFrame.prescribedH_hFirst frame η, h]
        simp [FLatticePaper.Induction.hFirst]
      exact row_eta_pos_H0 hL frame hS hpr (Rg.rH0.1 h).1 (Rg.rH0.1 h).2
    · have hpr : ∀ j, C.policy FLatticePaper.Induction.hFirst j ↔ j = (1, 1) := by
        intro j
        rw [C.prescribed.1 _ hz hw j, ChildFrame.prescribedH_hFirst frame η, h]
        simp [FLatticePaper.Induction.hFirst]
      exact row_eta_neg_H0 hL hpr (Rg.rH0.2 h).1 (Rg.rH0.2 h).2.1 (Rg.rH0.2 h).2.2
  by_cases h2 : z = frame.hLast
  · subst h2
    have e1 : ((0:ℤ), (-1:ℤ)) + frame.child.modifiedDeck.combine 1 0 = frame.hLast := by
      rw [combine_one_zero frame]; simp only [ChildFrame.hLast]; ext <;> (simp; try ring)
    have hpr : ∀ j, C.policy (0, -1) j ↔ j = (0, 0) := by
      intro j
      rw [hPol (0, -1) j, e1, C.prescribed.1 _ hz hw (j + frame.child.modifiedDeck.combine 1 0), prescribedH_hLast frame η,
        combine_one_zero frame]
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, ChildFrame.hLast]
      constructor <;> intro h <;> omega
    have hrep := row_Hlast hL frame hS hpr Rg.rHlast.1 Rg.rHlast.2
    have hA := parentSquareOut_add (evenSite_combine_one_zero frame) hPol hTr hrep
    rw [e1] at hA
    exact hA
  by_cases h3 : z = (2, 0)
  · subst h3
    have hpr : ∀ j, C.policy (2, 0) j ↔ j = (3, 0) := by
      intro j
      rw [C.prescribed.1 _ hz hw j, prescribedH_even frame η (by decide : EvenSite ((2:ℤ), (0:ℤ)))]
      have e : ((2:ℤ), (0:ℤ)) + ((1:ℤ), (0:ℤ)) = (3, 0) := by norm_num
      rw [e]
    rcases hη with h | h
    · exact row_eta_pos_H1 hL frame hS hpr (Rg.rH1.1 h).1 (Rg.rH1.1 h).2
    · exact row_eta_neg_H1 hL frame hS hpr (Rg.rH1.2 h).1 (Rg.rH1.2 h).2
  by_cases hodd : EvenSite z
  · rcases freeH_split frame hz h1 with hax | hdg
    · exact internal_H_case3 C hbin hz hw hodd rfl (Rg.h3 z hz h3 hw hodd hax).1 (Rg.h3 z hz h3 hw hodd hax).2.1
        (Rg.h3 z hz h3 hw hodd hax).2.2
    · exact internal_H_case2 C hbin hz hw hodd rfl (Rg.h2 z hz hw hodd hdg).1 (Rg.h2 z hz hw hodd hdg).2.1
        (Rg.h2 z hz hw hodd hdg).2.2
  · exact internal_H_case1 C hbin hz hw hodd h1 h2 rfl (Rg.h1 z hz hw hodd h1 h2).1 (Rg.h1 z hz hw hodd h1 h2).2.1
      (Rg.h1 z hz hw hodd h1 h2).2.2

/-- **The vertical parent-square witnesses for every odd free V root with zero Laplacian**, for the sign `η`. -/
theorem hVodd_of_routes {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hη : η = 1 ∨ η = -1) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (Rg : RouteGenuine C) :
    ∀ z ∈ frame.freeV, ¬ EvenSite z → laplacian G z = 0 → ParentSquareOut G C.policy z := by
  intro z hz hodd hw
  have hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0 := hP.binary
  have hS : frame.HasStrips G := hP.strips
  have hL : LocalRetention G C.policy := LocalRetention.of_canonical C hbin
  have hPol : ∀ x u, C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine 0 1) (u + frame.child.modifiedDeck.combine 0 1) :=
    fun x u => hdeck 0 1 x u
  have hTr : ∀ x, laplacian G (x + frame.child.modifiedDeck.combine 0 1) = laplacian G x := by
    intro x; rw [combine_zero_one frame]; exact StripColours.lap_add_transverse frame hP.periods x
  by_cases hexc : (η = -1 ∧ z = (0, 1)) ∨ (η = 1 ∧ z = (frame.vLast.1, frame.vLast.2 - 1))
  · rcases hexc with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have hpr : ∀ j, C.policy (0, 1) j ↔ j = (0, 2) := by
        intro j
        rw [C.prescribed.2 _ hz hw j, prescribedV_odd frame η hodd, h]
        norm_num
      exact row_eta_neg_V1 hL frame hS hpr (Rg.rV1 h).1 (Rg.rV1 h).2
    · have e1 : ((1:ℤ), (-2:ℤ)) + frame.child.modifiedDeck.combine 0 1 = (frame.vLast.1, frame.vLast.2 - 1) := by
        rw [combine_zero_one frame]; simp only [ChildFrame.vLast]; ext <;> simp <;> ring
      have hpr : ∀ j, C.policy (1, -2) j ↔ j = (1, -3) := by
        intro j
        rw [hPol (1, -2) j, e1, C.prescribed.2 _ hz hw (j + frame.child.modifiedDeck.combine 0 1),
          prescribedV_odd frame η hodd, h, combine_zero_one frame]
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, ChildFrame.vLast]
        constructor <;> intro h' <;> omega
      have hrep := row_eta_pos_Vprev hL frame hS hpr (Rg.rVprev h).1 (Rg.rVprev h).2
      have hA := parentSquareOut_add (evenSite_combine_zero_one frame) hPol hTr hrep
      rw [e1] at hA
      exact hA
  · have hz' : (z.1, z.2) ∈ frame.freeV := hz
    have hne3 : ¬ (η = -1 ∧ z = (0, 1)) := fun h => hexc (Or.inl h)
    rcases freeV_split frame hη hz hodd with hax | hdg
    · exact internal_V_case3 C hbin (δ := -η) rfl hη hz hw hodd rfl (Rg.v3 z hz hne3 hw hodd hax).1
        (Rg.v3 z hz hne3 hw hodd hax).2.1 (Rg.v3 z hz hne3 hw hodd hax).2.2
    · exact internal_V_case2 C hbin (δ := -η) rfl hη hz hw hodd rfl (Rg.v2 z hz hw hodd hdg).1
        (Rg.v2 z hz hw hodd hdg).2.1 (Rg.v2 z hz hw hodd hdg).2.2

end FLatticePaper.FreeRoutes

namespace FLatticePaper.FreeRoutes

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1NonfreeOut FLatticePaper.AndOrRank

/-- **`hfree_of_classes` with `hH` and `hVodd` assembled from the canonical games and the genuine route facts.** The chain's
remaining inputs (`hX3`, `hX1`, `hX2`, `hcanon`) are passed through unchanged. -/
theorem hfree_assembled {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η δ : ℤ}
    (hη : η = -δ) (hδ : δ = 1 ∨ δ = -1) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (Gm : CanonicalSignedGames frame G) (hη' : η = 1 ∨ η = -1)
    (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η) (hW : W.retained = (Gm.game η hη').policy)
    (Rg : RouteGenuine (Gm.game η hη'))
    (hX3 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      (z.1, z.2 - δ) ∈ frame.freeV ∧ laplacian G (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = -1 ∨ (laplacian G (z.1 + δ, z.2) = 0 ∧ Nonfree frame (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian G (z.1 + δ, z.2 - δ) = 0 ∧ Nonfree frame (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      (η = -1 ∨ z ≠ frame.vLast) → laplacian G z = 0 →
      laplacian G (z.1 + δ, z.2) = 0 → laplacian G (z.1 + δ, z.2 - δ) = -1 →
      W.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ))
    {z : Site} (hnf : ¬ Nonfree frame z) (hw : laplacian G z = 0) :
    ParentSquareOut G W.retained z :=
  FLatticePaper.ChainWire.hfree_of_classes hη hδ hP hW1 (Gm.game η hη') W hW (FLatticePaper.ChainWire.deck_of_games Gm hη' W hW)
    (fun z hz hw' => by
      rw [hW]; exact hH_of_routes (Gm.game η hη') hη' hP (Gm.deckEquiv η hη') Rg z hz hw')
    (fun z hz hodd hw' => by
      rw [hW]; exact hVodd_of_routes (Gm.game η hη') hη' hP (Gm.deckEquiv η hη') Rg z hz hodd hw')
    hX3 hX1 hX2 hcanon hnf hw

end FLatticePaper.FreeRoutes
