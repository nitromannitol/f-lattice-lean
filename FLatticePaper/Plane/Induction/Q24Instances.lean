import FLatticePaper.Plane.Induction.Q24Policy
import FLatticePaper.Plane.Induction.MinPolicy

/-! Task 72 / Q24: the chain instance of the abstract pair `PairData` (`Q24Policy.lean`): `A = F`, `B = g = F(· + ησ)`, the F-policy
`C` and the translated opposite policy `O`. The symmetric instance `(g, F)` is `PairData.swap` of this one, so no second construction is
needed. The square clauses of the translated `B`-selection are the square clauses of `F` at shifted squares (`sq_shift`). -/

namespace FLatticePaper.Q24Instances

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1MRank FLatticePaper.MinPolicy
  FLatticePaper.Q24Policy FLatticePaper.AndOrRank

variable {frame : ChildFrame} {F : Field} {η : ℤ}

/-- The F-side rank of a site (`KA`): the price, the rounded slip and the F-policy rank. -/
def rankF (C : CanonicalSignedPolicy frame F η) (x : Site) : Lex (ℤ × Lex (ℤ × ℤ)) :=
  toLex (frame.price F x, toLex (frame.cutGrade F 0 1 η x, C.rank x))

/-- The g-side rank of a site (`KB`): the price, rounded slip and rank of the opposite policy at `x + ησ`. -/
def rankG (O : CanonicalSignedPolicy frame F (-η)) (x : Site) : Lex (ℤ × Lex (ℤ × ℤ)) :=
  toLex (frame.price F (x + η • frame.shortShift),
    toLex (frame.cutGrade F 0 1 (-η) (x + η • frame.shortShift), O.rank (x + η • frame.shortShift)))

theorem incomingNeg_add_even (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingNeg (x + s) = incomingNeg x + s := by
  have h : EvenSite (x + s) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · have hx' : EvenSite (x + s) := h.mpr hx
    unfold incomingNeg
    rw [if_pos hx, if_pos hx']
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · have hx' : ¬ EvenSite (x + s) := fun h' => hx (h.mp h')
    unfold incomingNeg
    rw [if_neg hx, if_neg hx']
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

theorem incomingPos_add_even (x s : Site) (hs : (s.1 + s.2) % 2 = 0) :
    incomingPos (x + s) = incomingPos x + s := by
  have h : EvenSite (x + s) ↔ EvenSite x := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  by_cases hx : EvenSite x
  · have hx' : EvenSite (x + s) := h.mpr hx
    unfold incomingPos
    rw [if_pos hx, if_pos hx']
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · have hx' : ¬ EvenSite (x + s) := fun h' => hx (h.mp h')
    unfold incomingPos
    rw [if_neg hx, if_neg hx']
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

/-- An edge of the translated centre comes from an edge of the centre. -/
theorem edge_unshift (frame : ChildFrame) (hη : η = 1 ∨ η = -1) {x c : Site}
    (h : Edge (x + η • frame.shortShift) (c + η • frame.shortShift)) : Edge x c := by
  have hpar := shift_even frame hη
  unfold Edge at h ⊢
  rcases h with h | h
  · left
    rw [incomingNeg_add_even c _ hpar] at h
    exact add_right_cancel h
  · right
    rw [incomingPos_add_even c _ hpar] at h
    exact add_right_cancel h

/-- The translated opposite selection of a `g`-white centre: an input of the centre, with `D` at least `D(centre)`. -/
theorem O_sel_spec (O : CanonicalSignedPolicy frame F (-η)) (hη : η = 1 ∨ η = -1) {c : Site}
    (hw : laplacian F (c + η • frame.shortShift) = 0) :
    (O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingNeg c ∨
      O.sel (c + η • frame.shortShift) - η • frame.shortShift = incomingPos c) ∧
    frame.slip F η c ≤ frame.slip F η (O.sel (c + η • frame.shortShift) - η • frame.shortShift) ∧
    O.policy (c + η • frame.shortShift) (O.sel (c + η • frame.shortShift)) := by
  have hpar := shift_even frame hη
  have hpol : O.policy (c + η • frame.shortShift) (O.sel (c + η • frame.shortShift)) :=
    (O.white_policy _ hw _).mpr rfl
  refine ⟨?_, ?_, hpol⟩
  · rcases O.sel_input _ hw with h | h
    · left
      rw [h, incomingNeg_add_even c _ hpar, add_sub_cancel_right]
    · right
      rw [h, incomingPos_add_even c _ hpar, add_sub_cancel_right]
  · exact slip_le_of_G O (by rw [sub_add_cancel]; exact hpol)

/-- At a `g`-black centre the opposite policy keeps both inputs of the translated centre. -/
theorem O_keeps_of_black (O : CanonicalSignedPolicy frame F (-η)) (hη : η = 1 ∨ η = -1) {c x : Site}
    (hb : laplacian F (c + η • frame.shortShift) = -1) (hx : x = incomingNeg c ∨ x = incomingPos c) :
    O.policy (c + η • frame.shortShift) (x + η • frame.shortShift) := by
  have hpar := shift_even frame hη
  have hq := O.quota.1 _ hb
  rcases hx with rfl | rfl
  · rw [← incomingNeg_add_even c _ hpar]
    exact hq.1
  · rw [← incomingPos_add_even c _ hpar]
    exact hq.2

/-- The Laplacian of the translated `g` at a centre is the Laplacian of `F` at the translated centre. -/
theorem lap_g_iff (frame : ChildFrame) (hη : η = 1 ∨ η = -1) (c : Site) :
    laplacian (gF frame F η) c = laplacian F (c + η • frame.shortShift) :=
  lap_gF_eq_shift hη c

/-- The divergence `D = F − g` is the slip. -/
theorem Dd_gF (x : Site) : Dd F (gF frame F η) x = frame.slip F η x := by
  unfold Dd
  rw [slip_eq_gF]

/-- **Square clauses under an even shift.** The square clauses of the translated field with the translated selection are the square
clauses of `F` at the shifted square. -/
theorem mem_squareCorners_shift (a b : ℤ) (s x : Site) :
    x ∈ squareCorners a b ↔ x + s ∈ squareCorners (a + s.1) (b + s.2) := by
  unfold squareCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  omega

theorem kept_shift (sel : Site → Site) {a b : ℤ} {s : Site} (hs : EvenSite s) (c : Site) :
    keptInside (fun x => F (x + s)) (fun y => sel (y + s) - s) (squareCorners a b) c ↔
      keptInside F sel (squareCorners (a + s.1) (b + s.2)) (c + s) := by
  have hpar : (s.1 + s.2) % 2 = 0 := hs
  have hN : incomingNeg c ∈ squareCorners a b ↔ incomingNeg (c + s) ∈ squareCorners (a + s.1) (b + s.2) := by
    rw [incomingNeg_add_even c s hpar]
    exact mem_squareCorners_shift a b s _
  have hP : incomingPos c ∈ squareCorners a b ↔ incomingPos (c + s) ∈ squareCorners (a + s.1) (b + s.2) := by
    rw [incomingPos_add_even c s hpar]
    exact mem_squareCorners_shift a b s _
  have hSel : sel (c + s) - s ∈ squareCorners a b ↔ sel (c + s) ∈ squareCorners (a + s.1) (b + s.2) := by
    rw [mem_squareCorners_shift a b s, sub_add_cancel]
  unfold keptInside
  rw [laplacian_translate_of_even F c s hs]
  by_cases hL : laplacian F (c + s) = -1
  · simp only [hL, if_true, hN, hP]
  · simp only [hL, if_false, hSel]

/-- The square clause of the translated field is the square clause of `F` at the shifted square. -/
theorem sq_shift (sel : Site → Site) (a b : ℤ) (s : Site) (hs : EvenSite s) :
    SquareClauseSat (fun x => F (x + s)) (fun y => sel (y + s) - s) a b ↔
      SquareClauseSat F sel (a + s.1) (b + s.2) := by
  unfold SquareClauseSat
  constructor
  · intro h hall
    apply h
    intro c hc
    exact (kept_shift sel hs c).mpr (hall (c + s) ((mem_squareCorners_shift a b s c).mp hc))
  · intro h hall
    apply h
    intro c' hc'
    have hm : c' - s ∈ squareCorners a b := by
      rw [mem_squareCorners_shift a b s, sub_add_cancel]
      exact hc'
    have := (kept_shift sel hs (c' - s)).mp (hall (c' - s) hm)
    rwa [sub_add_cancel] at this

/-- **The chain pair.** `A = F` with the F-policy `C`; `B = g` with the translated opposite policy `O`. -/
def pairFG (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) :
    PairData F (gF frame F η) (Lex (ℤ × Lex (ℤ × ℤ))) where
  pA := C.policy
  selA := C.sel
  pB := fun c i => O.policy (c + η • frame.shortShift) (i + η • frame.shortShift)
  selB := fun c => O.sel (c + η • frame.shortShift) - η • frame.shortShift
  KA := rankF C
  KB := rankG O
  binA := hbin
  binB := fun c => by
    rw [lap_g_iff frame hη c]
    exact hbin _
  pA_edge := fun c i h => C.policyEdge c i h
  pB_edge := fun c i h => edge_unshift frame hη (O.policyEdge _ _ h)
  selA_input := C.sel_input
  pA_white := fun c hc i => C.white_policy c hc i
  pA_black := C.quota.1
  squaresA := C.squares
  pA_mono := fun c i h => by
    rw [Dd_gF, Dd_gF]
    exact slip_le_of_F C h
  pA_key := fun c i h _ => lex_of_canonical C h
  selB_input := fun c hc => by
    have hw : laplacian F (c + η • frame.shortShift) = 0 := by
      rw [← lap_g_iff frame hη c]
      exact hc
    exact (O_sel_spec O hη hw).1
  pB_white := fun c hc i => by
    have hw : laplacian F (c + η • frame.shortShift) = 0 := by
      rw [← lap_g_iff frame hη c]
      exact hc
    rw [O.white_policy _ hw, eq_sub_iff_add_eq]
  pB_black := fun c hb => by
    have hw : laplacian F (c + η • frame.shortShift) = -1 := by
      rw [← lap_g_iff frame hη c]
      exact hb
    exact ⟨O_keeps_of_black O hη hw (Or.inl rfl), O_keeps_of_black O hη hw (Or.inr rfl)⟩
  squaresB := fun a b => (sq_shift (F := F) O.sel a b (η • frame.shortShift) (shift_even frame hη)).mpr (O.squares _ _)
  pB_mono := fun c i h => by
    rw [Dd_gF, Dd_gF]
    exact slip_le_of_G O h
  pB_key := fun c i h _ => lex_of_canonical O h

/-- An edge translates to an edge of the translated centres. -/
theorem edge_shift (frame : ChildFrame) (hη : η = 1 ∨ η = -1) {x c : Site} (h : Edge x c) :
    Edge (x + η • frame.shortShift) (c + η • frame.shortShift) := by
  have hpar := shift_even frame hη
  unfold Edge at h ⊢
  rcases h with h | h
  · left
    rw [incomingNeg_add_even c _ hpar, h]
  · right
    rw [incomingPos_add_even c _ hpar, h]

/-- **Both roots are unforced at a rising edge of the chain.** At a retained F-edge `z → u` of `C` with `Φ_η z < Φ_η u`, the F-literal
`C.sel z` and the g-literal `O.sel (z + ησ) − ησ` at `z` are not forced: the F-root is `z` and the g-root is `z + ησ` in F-coordinates. -/
theorem rise_both_chain (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hUp : HasUnitPrice frame F) {z u : Site} (hC : C.policy z u)
    (hrise : frame.chainPotential F η z < frame.chainPotential F η u) :
    ¬ ForcedEdge F (fun _ _ => False) z (C.sel z) ∧
      ¬ ForcedEdge (gF frame F η) (fun _ _ => False) z (O.sel (z + η • frame.shortShift) - η • frame.shortShift) := by
  have hPB : ∀ c i, (pairFG C O hη hbin).pB c i →
      frame.price F (i + η • frame.shortShift) ≤ frame.price F (c + η • frame.shortShift) := by
    intro c i h
    have h' : O.policy (c + η • frame.shortShift) (i + η • frame.shortShift) := h
    have hm := O.nonincreasingP _ _ h'
    rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at hm
    exact hm
  have hPu : ∀ c i, Edge i c →
      frame.price F (i + η • frame.shortShift) - frame.price F (c + η • frame.shortShift) ≤ 1 := by
    intro c i h
    have hu := (hUp _ _ (edge_shift frame hη h)).2
    unfold priceIncrement at hu
    exact hu
  have hrise' : Dd F (gF frame F η) z + frame.price F (z + η • frame.shortShift) <
      Dd F (gF frame F η) u + frame.price F (u + η • frame.shortShift) := by
    unfold ChildFrame.chainPotential at hrise
    rw [Dd_gF, Dd_gF]
    exact hrise
  exact rise_both (pairFG C O hη hbin) (fun x => frame.price F (x + η • frame.shortShift)) hPB hPu hC hrise'

/-- The membership of a translated square corner, read back to the translated square. -/
theorem mem_shift_back (a b : ℤ) (s x : Site) :
    x ∈ squareCorners (a - s.1) (b - s.2) ↔ x + s ∈ squareCorners a b := by
  rw [mem_squareCorners_shift (a - s.1) (b - s.2) s, sub_add_cancel, sub_add_cancel]

/-- **Forced literals under an even shift.** A forced literal of `F` at the shifted centre is a forced literal of the translated field
`F(· + s)` at the centre: `ForcedEdge F (c + s) (i + s)` gives `ForcedEdge (F(· + s)) c i`. -/
theorem forcedEdge_shift (s : Site) (hs : EvenSite s) {c i : Site}
    (h : ForcedEdge F (fun _ _ => False) c i) :
    ∀ c0 i0, c = c0 + s → i = i0 + s → ForcedEdge (fun x => F (x + s)) (fun _ _ => False) c0 i0 := by
  have hpar : (s.1 + s.2) % 2 = 0 := hs
  induction h with
  | seed hs' => exact fun _ _ _ _ => False.elim hs'
  | @unit a b c o inside hc hw ho hout hin hforced ih =>
    intro c0 i0 hc0 hi0
    subst hc0
    subst hi0
    refine ForcedEdge.unit (a := a - s.1) (b := b - s.2) (inside := fun x => inside (x + s) - s) ?_ ?_ ?_ ?_ ?_ ?_
    · exact (mem_shift_back a b s c0).mpr hc
    · rw [laplacian_translate_of_even F c0 s hs]
      exact hw
    · rcases ho with ho | ho
      · left
        rw [incomingNeg_add_even c0 s hpar] at ho
        exact add_right_cancel ho
      · right
        rw [incomingPos_add_even c0 s hpar] at ho
        exact add_right_cancel ho
    · intro hmem
      exact hout ((mem_shift_back a b s i0).mp hmem)
    · intro c' hc' hne
      have hc'' : c' + s ∈ squareCorners a b := (mem_shift_back a b s c').mp hc'
      have hne'' : c' + s ≠ c0 + s := fun h' => hne (add_right_cancel h')
      rcases hin (c' + s) hc'' hne'' with h1 | ⟨h2, h3, h4⟩
      · left
        rw [laplacian_translate_of_even F c' s hs]
        exact h1
      · right
        refine ⟨by rw [laplacian_translate_of_even F c' s hs]; exact h2, ?_, ?_⟩
        · exact (mem_shift_back a b s _).mpr (by rw [sub_add_cancel]; exact h3)
        · rw [incomingNeg_add_even c' s hpar, incomingPos_add_even c' s hpar] at h4
          rcases h4 with h4 | h4
          · left
            exact sub_eq_of_eq_add h4
          · right
            exact sub_eq_of_eq_add h4
    · intro c' hc' hne hlap
      have hc'' : c' + s ∈ squareCorners a b := (mem_shift_back a b s c').mp hc'
      have hne'' : c' + s ≠ c0 + s := fun h' => hne (add_right_cancel h')
      have hlapF : laplacian F (c' + s) = 0 := by
        rw [← laplacian_translate_of_even F c' s hs]
        exact hlap
      exact ih (c' + s) hc'' hne'' hlapF c' (inside (c' + s) - s) rfl (sub_add_cancel _ _).symm

/-- **The roots of a rise lie outside the strict interior (the W1 input).** Given `W1Forced` of the word's frame (every F-white strict-interior
centre is forced), the two roots of a rising chain edge are not strict-interior centres: the F-root `z` (with its F-literal `C.sel z`
unforced), and the g-root `z + ησ` (whose translated g-literal is unforced). Hence each root is nonfree, unless free at a deck translate. -/
theorem rise_roots_not_SI (C : CanonicalSignedPolicy frame F η) (O : CanonicalSignedPolicy frame F (-η))
    (hη : η = 1 ∨ η = -1) (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hUp : HasUnitPrice frame F)
    (hW1word : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F) {z u : Site} (hC : C.policy z u)
    (hrise : frame.chainPotential F η z < frame.chainPotential F η u) :
    ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z ∧
      ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + η • frame.shortShift) := by
  obtain ⟨hz, hgz, -, -⟩ := rise_reduction (pairFG C O hη hbin) (fun x => frame.price F (x + η • frame.shortShift))
    (by
      intro c i h
      have h' : O.policy (c + η • frame.shortShift) (i + η • frame.shortShift) := h
      have hm := O.nonincreasingP _ _ h'
      rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at hm
      exact hm)
    (by
      intro c i h
      have hu := (hUp _ _ (edge_shift frame hη h)).2
      unfold priceIncrement at hu
      exact hu) hC (by
        unfold ChildFrame.chainPotential at hrise
        rw [Dd_gF, Dd_gF]
        exact hrise)
  have hlapz : laplacian F (z + η • frame.shortShift) = 0 := by
    rw [← lap_g_iff frame hη z]
    exact hgz
  have hunf := rise_both_chain C O hη hbin hUp hC hrise
  constructor
  · intro hSI
    obtain ⟨o, ho⟩ := hW1word z hSI hz
    have hfo := FLatticePaper.W1.forcedEdgeIn_forced ho
    have he : C.sel z = o :=
      forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h => False.elim h) C.squares z o hfo
    apply hunf.1
    rw [he]
    exact hfo
  · intro hSI
    obtain ⟨o, ho⟩ := hW1word _ hSI hlapz
    have hfo := FLatticePaper.W1.forcedEdgeIn_forced ho
    have hsh : ForcedEdge (fun x => F (x + η • frame.shortShift)) (fun _ _ => False) z
        (o - η • frame.shortShift) :=
      forcedEdge_shift (F := F) (η • frame.shortShift) (shift_even frame hη) hfo z _ rfl
        (sub_add_cancel _ _).symm
    have he : (pairFG C O hη hbin).selB z = o - η • frame.shortShift :=
      forcedB_eq_selB (pairFG C O hη hbin) hsh
    apply hunf.2
    rw [← he] at hsh
    exact hsh

end FLatticePaper.Q24Instances
