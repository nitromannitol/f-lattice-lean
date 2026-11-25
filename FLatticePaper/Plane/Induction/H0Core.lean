import FLatticePaper.Plane.Induction.RetainedCore
import FLatticePaper.Plane.Induction.FanTerminal
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.W1Exit

/-! # The `H_0` core (Q23 step 4): the minus and the plus candidates

The core removes the candidates of the last row entries. The strict-interior part of a fort is empty by `RetainedCore.interior_empty_of_retained`
(the retained-quota fort of the W1 policy, with rank `Rk`; the retained structure `(G, R, Rk)` is supplied by the policy).

* Minus (`h0_core_minus`): the candidates `H_0 = (1,0)`, `V_0 = (0,0)` in `E`. `H_0 ∈ S` forces `(1,1) ∈ S` (its south input `(1,−1)` is outside
  `E`), and `(1,1)` is open; `V_0 ∈ S` forces `H_0 ∈ S` (its west input `(−1,0)` is outside `E`).
* Plus (`plus_core`): the candidates `H_0 = (1,0)`, `V_{−1} = (1,−1)` in `E − V`, with `V = (n−d, n+d)` and the translated chart
  `M(z + V)`. `H_0 ∈ S` forces `V_{−1} ∈ S` (its north input `(1,1)` is outside `E − V`), and `V_{−1} ∈ S` forces `(2,−1) ∈ S`
  (its west input `(0,−1)` is outside `E − V`), and `(2,−1)` is open in `E − V`.

The candidates are not called from the strict interior: the geometry of the open rectangle (`minus_not_called`, `plus_not_called`). -/

namespace FLatticePaper.H0Core

open FLatticePaper FLatticePaper.Induction FLatticePaper.FanTerminal FLatticePaper.RetainedCore

/-- `(1, −1)` (the south input of `H_0`) is outside the closed polygon. -/
theorem not_closed_one_neg (frame : ChildFrame) : (1, -1) ∉ frame.closedPolygon := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  have h1 : frame.tGrade ((1 : ℤ), (-1 : ℤ)) = frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade; ring
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos (show EvenSite ((1 : ℤ), (-1 : ℤ)) by unfold EvenSite; simp)]
  intro h
  have := h.2.1
  rw [h1] at this
  omega

/-- `(−1, 0)` (the west input of `V_0`) is outside the closed polygon. -/
theorem not_closed_neg_one_zero (frame : ChildFrame) : (-1, 0) ∉ frame.closedPolygon := by
  obtain ⟨-, -, -, hd3, hT⟩ := frame.child_facts
  have hs : frame.sGrade ((-1 : ℤ), (0 : ℤ)) = -(frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_neg (show ¬ EvenSite ((-1 : ℤ), (0 : ℤ)) by unfold EvenSite; simp)]
  intro h
  have := h.2.2.1
  rw [hs] at this
  have hn := (frame.child_facts).1
  omega

/-- `(1, 1)` is in the open rectangle. -/
theorem open_one_one (frame : ChildFrame) : frame.openRect (1, 1) := by
  obtain ⟨hn, hnd, -, hd3, hT⟩ := frame.child_facts
  have hev : EvenSite ((1 : ℤ), (1 : ℤ)) := by unfold EvenSite; simp
  have ht : frame.tGrade ((1 : ℤ), (1 : ℤ)) = frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hs : frame.sGrade ((1 : ℤ), (1 : ℤ)) = 2 * frame.child.den := by
    unfold ChildFrame.sGrade; ring
  unfold ChildFrame.openRect
  rw [if_pos hev, ht, hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · omega
  · omega
  · nlinarith

/-- The minus candidate sites are not open: `(2,0)`, `(0,0)`, `(0,1)`, `(0,−1)`. -/
theorem not_open_two_zero (frame : ChildFrame) : ¬ frame.openRect (2, 0) := by
  intro h
  unfold ChildFrame.openRect at h
  rw [if_pos (show EvenSite ((2 : ℤ), (0 : ℤ)) by unfold EvenSite; simp)] at h
  have ht : frame.tGrade ((2 : ℤ), (0 : ℤ)) = 2 * frame.child.num := by unfold ChildFrame.tGrade; ring
  rw [ht] at h
  have hn := (frame.child_facts).1
  omega

theorem not_open_zero_zero (frame : ChildFrame) : ¬ frame.openRect (0, 0) := by
  intro h
  unfold ChildFrame.openRect at h
  rw [if_pos (show EvenSite ((0 : ℤ), (0 : ℤ)) by unfold EvenSite; simp)] at h
  have hs : frame.sGrade ((0 : ℤ), (0 : ℤ)) = 0 := by unfold ChildFrame.sGrade; ring
  rw [hs] at h
  have hn := (frame.child_facts).1
  omega

theorem not_open_zero_one (frame : ChildFrame) : ¬ frame.openRect (0, 1) := by
  intro h
  unfold ChildFrame.openRect at h
  rw [if_neg (show ¬ EvenSite ((0 : ℤ), (1 : ℤ)) by unfold EvenSite; simp)] at h
  have hs : frame.sGrade ((0 : ℤ), (1 : ℤ)) = frame.child.den - frame.child.num := by
    unfold ChildFrame.sGrade; ring
  rw [hs] at h
  have hn := (frame.child_facts).1
  omega

theorem not_open_zero_neg_one (frame : ChildFrame) : ¬ frame.openRect (0, -1) := by
  intro h
  unfold ChildFrame.openRect at h
  rw [if_neg (show ¬ EvenSite ((0 : ℤ), (-1 : ℤ)) by unfold EvenSite; simp)] at h
  have ht : frame.tGrade ((0 : ℤ), (-1 : ℤ)) = frame.child.den := by unfold ChildFrame.tGrade; ring
  rw [ht] at h
  have hnd := (frame.child_facts).2.1
  omega

/-- The inputs of an odd site are its vertical neighbours. -/
theorem incomingNeg_of_not_even (x : Site) (h : ¬ EvenSite x) : incomingNeg x = (x.1, x.2 - 1) := by
  unfold incomingNeg; rw [if_neg h]

theorem incomingPos_of_not_even (x : Site) (h : ¬ EvenSite x) : incomingPos x = (x.1, x.2 + 1) := by
  unfold incomingPos; rw [if_neg h]

theorem incomingNeg_of_even (x : Site) (h : EvenSite x) : incomingNeg x = (x.1 - 1, x.2) := by
  unfold incomingNeg; rw [if_pos h]

theorem incomingPos_of_even (x : Site) (h : EvenSite x) : incomingPos x = (x.1 + 1, x.2) := by
  unfold incomingPos; rw [if_pos h]

/-- A fort point whose south (or north) input is outside the fort has the other input in the fort. -/
theorem fort_pos_of_neg_not_fortAt {N : Site → Prop} {F : Field} {S : Set Site} {c : Site} (hfort : FortAt N F S) (hN : N c)
    (hc : c ∈ S) (hn : incomingNeg c ∉ S) : incomingPos c ∈ S := by
  rcases hfort c hc hN with ⟨-, hsome⟩ | ⟨-, hn', hp⟩
  · exact hsome.resolve_left hn
  · exact absurd hn' hn

/-- A fort point whose south (or north) input is outside the fort has the other input in the fort (the unrestricted fort). -/
theorem fort_pos_of_neg_not {F : Field} {S : Set Site} {c : Site} (hfort : IsIncomingFort F S) (hc : c ∈ S)
    (hn : incomingNeg c ∉ S) : incomingPos c ∈ S :=
  fort_pos_of_neg_not_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) trivial hc hn

theorem fort_neg_of_pos_not_fortAt {N : Site → Prop} {F : Field} {S : Set Site} {c : Site} (hfort : FortAt N F S) (hN : N c)
    (hc : c ∈ S) (hp : incomingPos c ∉ S) : incomingNeg c ∈ S := by
  rcases hfort c hc hN with ⟨-, hsome⟩ | ⟨-, hn', hp'⟩
  · exact hsome.resolve_right hp
  · exact absurd hp' hp

/-- The converse of `fort_pos_of_neg_not` (the unrestricted fort). -/
theorem fort_neg_of_pos_not {F : Field} {S : Set Site} {c : Site} (hfort : IsIncomingFort F S) (hc : c ∈ S)
    (hp : incomingPos c ∉ S) : incomingNeg c ∈ S :=
  fort_neg_of_pos_not_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) trivial hc hp

/-- The minus candidates `H_0 = (1,0)`, `V_0 = (0,0)` are not inputs of an open site. -/
theorem minus_not_called (frame : ChildFrame) (x : Site) (hx : frame.openRect x) (k : Site)
    (hk : k = hFirst ∨ k = vFirst) : ¬ (k = incomingNeg x ∨ k = incomingPos x) := by
  obtain ⟨a, b⟩ := x
  rcases hk with rfl | rfl
  · rintro (h | h)
    · unfold hFirst at h
      by_cases hev : EvenSite (a, b)
      · rw [incomingNeg_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 2 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        exact not_open_two_zero frame hx
      · rw [incomingNeg_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        apply hev
        unfold EvenSite
        simp only
        omega
    · unfold hFirst at h
      by_cases hev : EvenSite (a, b)
      · rw [incomingPos_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        exact not_open_zero_zero frame hx
      · rw [incomingPos_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        apply hev
        unfold EvenSite
        simp only
        omega
  · rintro (h | h)
    · unfold vFirst at h
      by_cases hev : EvenSite (a, b)
      · rw [incomingNeg_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exfalso
        unfold EvenSite at hev
        simp only at hev
        omega
      · rw [incomingNeg_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 0 := by omega
        have hb : b = 1 := by omega
        subst ha; subst hb
        exact not_open_zero_one frame hx
    · unfold vFirst at h
      by_cases hev : EvenSite (a, b)
      · rw [incomingPos_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exfalso
        unfold EvenSite at hev
        simp only at hev
        omega
      · rw [incomingPos_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 0 := by omega
        have hb : b = -1 := by omega
        subst ha; subst hb
        exact not_open_zero_neg_one frame hx

/-- **The minus `H_0` core.** A fort of the policy field, in the closed polygon, whose boundary points are among `H_0, V_0`, is empty:
the retained-quota core (`interior_empty_of_retained`) empties the strict interior, and `H_0`, `V_0` force points of it. -/
theorem h0_core_minus_fortAt {M G : Field} {R : Site → Site → Prop} {Rk : Site → ℤ} (frame : ChildFrame)
    (hagree : ∀ y ∈ frame.closedPolygon, M y = G y) (hquota : RetainQuota G R)
    (hrank : ∀ c i, R c i → Rk i < Rk c) {S : Set Site} (hfort : FortAt (fun z => frame.openRect z) M S)
    (hcW : FortAt (fun z => z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((0 : ℤ), (0 : ℤ))) M S)
    (hsub : ∀ z ∈ S, z ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z → z = hFirst ∨ z = vFirst) : S = ∅ := by
  have hint := interior_empty_of_retained (P := frame.closedPolygon) (Q := fun z => frame.openRect z)
    (C := fun k => k = hFirst ∨ k = vFirst) (openRect_finite frame)
    (fun x hx i hi => FLatticePaper.W1Exit.rectInputs frame x hx i hi) hagree hquota hrank hfort hsub hcand
    (fun x hx k hk => minus_not_called frame x hx k hk)
  have hH0 : hFirst ∉ S := by
    intro h
    have hfirst : hFirst = (1, 0) := rfl
    rw [hfirst] at h
    have hn : ((1 : ℤ), (-1 : ℤ)) ∉ S := fun hm => not_closed_one_neg frame (hsub _ hm)
    have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_not_even _ hodd]; simp
    have hinP : incomingPos ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
      rw [incomingPos_of_not_even _ hodd]; simp
    have hmem : ((1 : ℤ), (1 : ℤ)) ∈ S := by
      have := fort_pos_of_neg_not_fortAt hcW (Or.inl rfl) h (by rw [hinN]; exact hn)
      rw [hinP] at this
      exact this
    exact hint (1, 1) hmem (open_one_one frame)
  have hV0 : vFirst ∉ S := by
    intro h
    have hvfirst : vFirst = (0, 0) := rfl
    rw [hvfirst] at h
    have hn : ((-1 : ℤ), (0 : ℤ)) ∉ S := fun hm => not_closed_neg_one_zero frame (hsub _ hm)
    have hev : EvenSite ((0 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((0 : ℤ), (0 : ℤ)) = ((-1 : ℤ), (0 : ℤ)) := by
      rw [incomingNeg_of_even _ hev]; simp
    have hinP : incomingPos ((0 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
      rw [incomingPos_of_even _ hev]; simp
    have hH : ((1 : ℤ), (0 : ℤ)) ∈ S := by
      have := fort_pos_of_neg_not_fortAt hcW (Or.inr rfl) h (by rw [hinN]; exact hn)
      rw [hinP] at this
      exact this
    exact hH0 hH
  ext z
  constructor
  · intro hz
    have hcz : z = hFirst ∨ z = vFirst := by
      by_cases hopen : frame.openRect z
      · exact absurd hopen (fun ho => hint z hz ho)
      · exact hcand z hz (hsub z hz) hopen
    rcases hcz with rfl | rfl
    · exact absurd hz hH0
    · exact absurd hz hV0
  · intro hz
    exact absurd hz (Set.notMem_empty z)

/-- **The minus core** (the unrestricted fort): `h0_core_minus_fortAt` with the fort at every site. -/
theorem h0_core_minus {M G : Field} {R : Site → Site → Prop} {Rk : Site → ℤ} (frame : ChildFrame)
    (hagree : ∀ y ∈ frame.closedPolygon, M y = G y) (hquota : RetainQuota G R)
    (hrank : ∀ c i, R c i → Rk i < Rk c) {S : Set Site} (hfort : IsIncomingFort M S)
    (hsub : ∀ z ∈ S, z ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z → z = hFirst ∨ z = vFirst) : S = ∅ :=
  h0_core_minus_fortAt frame hagree hquota hrank (fortAt_of_incoming hfort) (fortAt_of_incoming hfort) hsub hcand

/-- The translation vector of the plus core: `V = (n − d, n + d)`, of even coordinate sum `2n`. -/
def plusV (frame : ChildFrame) : Site := (frame.child.num - frame.child.den, frame.child.num + frame.child.den)

theorem plusV_even (frame : ChildFrame) : (plusV frame).1 + (plusV frame).2 = 2 * frame.child.num := by
  unfold plusV; simp only; ring

theorem incomingNeg_add_even (x v : Site) (hv : (v.1 + v.2) % 2 = 0) : incomingNeg (x + v) = incomingNeg x + v := by
  have hpar : EvenSite (x + v) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · rw [incomingNeg_of_even _ hx, incomingNeg_of_even _ (hpar.2 hx)]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; try ring
    · simp only [Prod.snd_add]; try ring
  · rw [incomingNeg_of_not_even _ hx, incomingNeg_of_not_even _ (fun h => hx (hpar.1 h))]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; try ring
    · simp only [Prod.snd_add]; try ring

theorem incomingPos_add_even (x v : Site) (hv : (v.1 + v.2) % 2 = 0) : incomingPos (x + v) = incomingPos x + v := by
  have hpar : EvenSite (x + v) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · rw [incomingPos_of_even _ hx, incomingPos_of_even _ (hpar.2 hx)]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; try ring
    · simp only [Prod.snd_add]; try ring
  · rw [incomingPos_of_not_even _ hx, incomingPos_of_not_even _ (fun h => hx (hpar.1 h))]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add]; try ring
    · simp only [Prod.snd_add]; try ring

theorem plus_site (frame : ChildFrame) (x y : ℤ) :
    ((x, y) : Site) + plusV frame = (x + (frame.child.num - frame.child.den), y + (frame.child.num + frame.child.den)) := rfl

/-- `(2,0) + V` is not open in `E − V` (`t = 2n − T`, and `d < n + 2` would be needed). -/
theorem plus_not_open_two_zero (frame : ChildFrame) : ¬ frame.openRect (((2 : ℤ), (0 : ℤ)) + plusV frame) := by
  obtain ⟨-, -, hd2, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.openRect at h
  rw [if_pos (show EvenSite (2 + (frame.child.num - frame.child.den), 0 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  rw [hT] at h
  simp only [ChildFrame.tGrade] at h
  nlinarith [h.1]

/-- `(0,0) + V = V` is not open in `E − V`. -/
theorem plus_not_open_zero_zero (frame : ChildFrame) : ¬ frame.openRect (((0 : ℤ), (0 : ℤ)) + plusV frame) := by
  obtain ⟨hn, hnd, -, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.openRect at h
  rw [if_pos (show EvenSite (0 + (frame.child.num - frame.child.den), 0 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  rw [hT] at h
  simp only [ChildFrame.tGrade] at h
  nlinarith [h.1]

/-- `(1,0) + V` is not open in `E − V` (`t = T`-shifted: `t ≥ d` would be needed below `n`). -/
theorem plus_not_open_one_zero (frame : ChildFrame) : ¬ frame.openRect (((1 : ℤ), (0 : ℤ)) + plusV frame) := by
  obtain ⟨-, -, hd2, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.openRect at h
  rw [if_neg (show ¬ EvenSite (1 + (frame.child.num - frame.child.den), 0 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  rw [hT] at h
  simp only [ChildFrame.tGrade] at h
  nlinarith [h.1]

/-- `(1,−2) + V` is not open in `E − V` (its `s = 3n − d` is below `d + n − 2`). -/
theorem plus_not_open_one_neg_two (frame : ChildFrame) :
    ¬ frame.openRect (((1 : ℤ), (-2 : ℤ)) + plusV frame) := by
  obtain ⟨-, -, hd2, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.openRect at h
  rw [if_neg (show ¬ EvenSite (1 + (frame.child.num - frame.child.den), -2 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  simp only [ChildFrame.sGrade] at h
  nlinarith [h.2.2.1]

/-- `(1,1) + V` is outside the closed polygon (`t = −T + n − d < 2 − T`). -/
theorem plus_not_closed_one_one (frame : ChildFrame) : ((1 : ℤ), (1 : ℤ)) + plusV frame ∉ frame.closedPolygon := by
  obtain ⟨-, -, hd2, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.closedPolygon at h
  simp only [Set.mem_setOf_eq] at h
  rw [if_pos (show EvenSite (1 + (frame.child.num - frame.child.den), 1 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  rw [hT] at h
  simp only [ChildFrame.tGrade] at h
  nlinarith [h.1]

/-- `(0,−1) + V` is outside the closed polygon (`s = n − d < 2 − d + n`). -/
theorem plus_not_closed_zero_neg_one (frame : ChildFrame) :
    ((0 : ℤ), (-1 : ℤ)) + plusV frame ∉ frame.closedPolygon := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [plus_site]
  intro h
  unfold ChildFrame.closedPolygon at h
  simp only [Set.mem_setOf_eq] at h
  rw [if_neg (show ¬ EvenSite (0 + (frame.child.num - frame.child.den), -1 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)] at h
  simp only [ChildFrame.sGrade] at h
  nlinarith [h.2.2.1]

/-- `(2,−1) + V` is open in `E − V` (`t = −T + 2n + d` and `s = d + 3n`). -/
theorem plus_open_two_neg_one (frame : ChildFrame) : frame.openRect (((2 : ℤ), (-1 : ℤ)) + plusV frame) := by
  obtain ⟨hn, hnd, hd2, -, hT⟩ := frame.child_facts
  rw [plus_site]
  unfold ChildFrame.openRect
  rw [if_neg (show ¬ EvenSite (2 + (frame.child.num - frame.child.den), -1 + (frame.child.num + frame.child.den)) by
    unfold EvenSite; simp only; ring_nf; omega)]
  rw [hT]
  simp only [ChildFrame.tGrade, ChildFrame.sGrade]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- The plus candidates `H_0 = (1,0)`, `V_{−1} = (1,−1)` (in `E − V`) are not inputs of a strict-interior point of `E − V`. -/
theorem plus_not_called (frame : ChildFrame) (z : Site) (hz : frame.openRect (z + plusV frame)) (k : Site)
    (hk : k = ((1 : ℤ), (0 : ℤ)) ∨ k = ((1 : ℤ), (-1 : ℤ))) : ¬ (k = incomingNeg z ∨ k = incomingPos z) := by
  obtain ⟨a, b⟩ := z
  rcases hk with rfl | rfl
  · rintro (h | h)
    · by_cases hev : EvenSite (a, b)
      · rw [incomingNeg_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 2 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        exact plus_not_open_two_zero frame hz
      · rw [incomingNeg_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact hev (by unfold EvenSite; simp only; omega)
    · by_cases hev : EvenSite (a, b)
      · rw [incomingPos_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        exact plus_not_open_zero_zero frame hz
      · rw [incomingPos_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact hev (by unfold EvenSite; simp only; omega)
  · rintro (h | h)
    · by_cases hev : EvenSite (a, b)
      · rw [incomingNeg_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exfalso
        unfold EvenSite at hev
        simp only at hev
        omega
      · rw [incomingNeg_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 1 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        exact plus_not_open_one_zero frame hz
    · by_cases hev : EvenSite (a, b)
      · rw [incomingPos_of_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exfalso
        unfold EvenSite at hev
        simp only at hev
        omega
      · rw [incomingPos_of_not_even _ hev] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ha : a = 1 := by omega
        have hb : b = -2 := by omega
        subst ha; subst hb
        exact plus_not_open_one_neg_two frame hz

/-- **The plus `H_0` core.** A fort `T` of the translated chart `M(· + V)` on `E − V`, whose boundary points are among `H_0`, `V_{−1}`,
is empty: `H_0 ∈ T` forces `V_{−1} = (1,−1) ∈ T` (its north input `(1,1)` is outside `E − V`), and `V_{−1} ∈ T` forces `(2,−1) ∈ T`
(its west input `(0,−1)` is outside), which is open in `E − V`. The retained structure `(G, R, Rk)` is the policy's, translated. -/
theorem plus_core_fortAt {M G : Field} {R : Site → Site → Prop} {Rk : Site → ℤ} (frame : ChildFrame)
    (hagree : ∀ y : Site, y + plusV frame ∈ frame.closedPolygon → M (y + plusV frame) = G y)
    (hquota : RetainQuota G R) (hrank : ∀ c i, R c i → Rk i < Rk c)
    {T : Set Site} (hfort : FortAt (fun z => frame.openRect (z + plusV frame)) (fun z => M (z + plusV frame)) T)
    (hcW : FortAt (fun z => z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) (fun z => M (z + plusV frame)) T)
    (hsub : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon → ¬ frame.openRect (z + plusV frame) →
      z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) : T = ∅ := by
  have hVe : ((plusV frame).1 + (plusV frame).2) % 2 = 0 := by rw [plusV_even]; omega
  have hfin : {x | frame.openRect (x + plusV frame)}.Finite :=
    ((openRect_finite frame).image (fun y => y - plusV frame)).subset
      (fun x hx => ⟨x + plusV frame, hx, by simp⟩)
  have hQin : ∀ x, frame.openRect (x + plusV frame) → ∀ i : Site,
      (i = incomingNeg x ∨ i = incomingPos x) → i + plusV frame ∈ frame.closedPolygon := by
    intro x hx i hi
    rcases hi with rfl | rfl
    · rw [← incomingNeg_add_even x (plusV frame) hVe]
      exact FLatticePaper.W1Exit.rectInputs frame (x + plusV frame) hx _ (Or.inl rfl)
    · rw [← incomingPos_add_even x (plusV frame) hVe]
      exact FLatticePaper.W1Exit.rectInputs frame (x + plusV frame) hx _ (Or.inr rfl)
  have hint := interior_empty_of_retained (P := {z | z + plusV frame ∈ frame.closedPolygon})
    (Q := fun z => frame.openRect (z + plusV frame)) (M := fun z => M (z + plusV frame)) (G := G) (R := R)
    (Rk := Rk) (C := fun k => k = ((1 : ℤ), (0 : ℤ)) ∨ k = ((1 : ℤ), (-1 : ℤ))) (S := T) hfin
    (fun x hx i hi => hQin x hx i hi)
    (fun y hy => hagree y hy) hquota hrank hfort hsub
    (fun z hz hzP hnQ => hcand z hz hzP hnQ)
    (fun x hx k hk => plus_not_called frame x hx k hk)
  have hint' : ∀ z ∈ T, ¬ frame.openRect (z + plusV frame) := fun z hz => hint z hz
  -- `V_{−1} ∈ T` forces `(2,−1) ∈ T`, an open point of `E − V`
  have hVm1 : ((1 : ℤ), (-1 : ℤ)) ∈ T → False := by
    intro h
    have hev : EvenSite ((1 : ℤ), (-1 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_even _ hev]; simp
    have hinP : incomingPos ((1 : ℤ), (-1 : ℤ)) = ((2 : ℤ), (-1 : ℤ)) := by
      rw [incomingPos_of_even _ hev]; simp
    have h2 : ((2 : ℤ), (-1 : ℤ)) ∈ T :=
      fort_pos_of_neg_not_fortAt hcW (Or.inr rfl) h (by rw [hinN]; exact fun hm => plus_not_closed_zero_neg_one frame (hsub _ hm))
    exact hint' _ h2 (plus_open_two_neg_one frame)
  -- `H_0 ∈ T` forces `V_{−1} ∈ T`
  have hH0 : ((1 : ℤ), (0 : ℤ)) ∉ T := by
    intro h
    have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; simp
    have hinN : incomingNeg ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (-1 : ℤ)) := by
      rw [incomingNeg_of_not_even _ hodd]; simp
    have hinP : incomingPos ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
      rw [incomingPos_of_not_even _ hodd]; simp
    have hm1 : ((1 : ℤ), (-1 : ℤ)) ∈ T :=
      fort_neg_of_pos_not_fortAt hcW (Or.inl rfl) h (by rw [hinP]; exact fun hm => plus_not_closed_one_one frame (hsub _ hm))
    exact hVm1 hm1
  ext z
  constructor
  · intro hz
    rcases hcand z hz (hsub z hz) (hint' z hz) with rfl | rfl
    · exact absurd hz hH0
    · exact absurd hz (fun h => hVm1 h)
  · intro hz
    exact absurd hz (Set.notMem_empty z)

/-- **The plus core** (the unrestricted fort): `plus_core_fortAt` with the fort at every site. -/
theorem plus_core {M G : Field} {R : Site → Site → Prop} {Rk : Site → ℤ} (frame : ChildFrame)
    (hagree : ∀ y : Site, y + plusV frame ∈ frame.closedPolygon → M (y + plusV frame) = G y)
    (hquota : RetainQuota G R) (hrank : ∀ c i, R c i → Rk i < Rk c)
    {T : Set Site} (hfort : IsIncomingFort (fun z => M (z + plusV frame)) T)
    (hsub : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon)
    (hcand : ∀ z ∈ T, z + plusV frame ∈ frame.closedPolygon → ¬ frame.openRect (z + plusV frame) →
      z = ((1 : ℤ), (0 : ℤ)) ∨ z = ((1 : ℤ), (-1 : ℤ))) : T = ∅ :=
  plus_core_fortAt frame hagree hquota hrank (fortAt_of_incoming hfort) (fortAt_of_incoming hfort) hsub hcand

end FLatticePaper.H0Core
