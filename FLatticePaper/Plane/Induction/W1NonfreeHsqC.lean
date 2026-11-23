import FLatticePaper.Plane.Induction.W1NonfreeHsqNonneg
import FLatticePaper.Plane.Induction.W1MReflect
import FLatticePaper.Plane.Induction.W1MFinal
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.SlipReflect
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.W1CollarFrame
import FLatticePaper.Plane.Induction.StrongPriceValues

/-! # Task 94: the `hsq` clause at strict centres with `Ψ c < 0` (the `C` side), off the collar

The `C` side is the centre reflection `z ↦ K − z` (`K` the sheet centre, even) of the `A` side. `Ψ(K − z) = −Ψ z` (`sheetDiffW_reflect`), the
sheet minimum's laplacian is reflection invariant (`sheetFacts_of_conjPacket`, `laplacian_reflect_of`), edges reflect with their labels
swapped (`neighbours_reflect`), and the square reflects (`square_reflect`). The `C`-policy at `K − p` is the `A`-policy at `p`
(`sheetPolicyC`). The `C`-pointer at `K − p` is `K − nx` by uniqueness of the `A`-pointer at `p` (`pointerOf_sheetC_reflect`). At a tie
corner, `hagree_M_tie_of_inherited` gives the common arrow, and the uniqueness at `p` identifies it with `K − nx`. The strictness of the
corners comes from the centre (`strict_corners_of_not_collar`), so no reflection of the collar is needed. -/

namespace FLatticePaper.W1NonfreeHsqC

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1MReflect

theorem tGrade_add' (frame : ChildFrame) (x y : Site) :
    frame.tGrade (x + y) = frame.tGrade x + frame.tGrade y := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The sheet minimum's laplacian is invariant under the centre reflection. -/
theorem lap_MW_reflect {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) :
    laplacian (MW word) ((frameAt word).centre - z) = laplacian (MW word) z := by
  refine FLatticePaper.W1MFinal.laplacian_reflect_of (MW word) (frameAt word).centre (frameAt word).evenSite_centre
    (fun x => (frameAt word).tGrade x) (frameAt word).symmetryConstant (tGrade_add' (frameAt word)) ?_ z
  intro w
  exact (sheetFacts_of_conjPacket hw hSE.packet).2.2.1 w

/-- `Ψ` is antisymmetric under the centre reflection. -/
theorem psi_reflect {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) : sheetPsi word ((frameAt word).centre - z) = -sheetPsi word z :=
  sheetDiffW_reflect hw hSE.packet z

/-- Edges reflect, with the two labels exchanged. -/
theorem edge_reflect (K : Site) (hK : (K.1 + K.2) % 2 = 0) (i x : Site) :
    Edge (K - i) (K - x) ↔ Edge i x := by
  have hx := neighbours_reflect K x hK
  have hx' := neighbours_reflect K (K - x) hK
  rw [sub_sub_cancel] at hx'
  unfold Edge
  constructor
  · rintro (h | h)
    · right
      calc i = K - (K - i) := (sub_sub_cancel K i).symm
        _ = incomingPos x := by rw [h, hx'.1]
    · left
      calc i = K - (K - i) := (sub_sub_cancel K i).symm
        _ = incomingNeg x := by rw [h, hx'.2]
  · rintro (h | h)
    · right
      rw [h]
      exact hx.1
    · left
      rw [h]
      exact hx.2

/-- A parent square with output gives a parent square. -/
theorem parentSquare_of_out {G : Field} {Q : Site → Site → Prop} {z : Site} (h : ParentSquareOut G Q z) :
    ParentSquare Q z := by
  obtain ⟨q0, q1, q2, o, a, b, hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3,
    hR0, hR1, hR2, -, -, -, -, -, -, -⟩ := h
  exact ⟨q0, q1, q2, a, b, hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3, hR0, hR1, hR2⟩

/-- The `C`-policy at `K − p` is the `A`-policy at `p`. -/
theorem policyC_of_A {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (Pd : OldPolicyData frame G seed η)
    (lv K : Site) {u v : Site} (h : sheetPolicyA Pd lv u v) : sheetPolicyC Pd lv K (K - u) (K - v) := by
  show sheetPolicyA Pd lv (K - (K - u)) (K - (K - v))
  rw [sub_sub_cancel, sub_sub_cancel]
  exact h

/-- The `C`-pointer at the reflected corner is the reflection of the `A`-pointer, by uniqueness of the `A`-pointer. -/
theorem pointerOf_sheetC_reflect {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (Pd : OldPolicyData frame G seed η) (lv K : Site) (hK : (K.1 + K.2) % 2 = 0) (p nx : Site)
    (hnx : Edge nx p) (hQ : sheetPolicyA Pd lv p nx) (hu : ∀ j, sheetPolicyA Pd lv p j → j = nx) :
    pointerOf (sheetPolicyC Pd lv K) (K - p) = K - nx := by
  have hin : Edge (K - nx) (K - p) := (edge_reflect K hK nx p).2 hnx
  have hQC : sheetPolicyC Pd lv K (K - p) (K - nx) := policyC_of_A Pd lv K hQ
  have huC : ∀ j, sheetPolicyC Pd lv K (K - p) j → j = K - nx := by
    intro j hj
    have h : sheetPolicyA Pd lv (K - (K - p)) (K - j) := hj
    rw [sub_sub_cancel] at h
    have := hu (K - j) h
    rw [← this, sub_sub_cancel]
  exact pointer_of_unique (sheetPolicyC Pd lv K) (K - p) (K - nx) hin hQC huC

/-- The `sheetOut` at a site with `Ψ < 0` is its `C`-pointer. -/
theorem sheetOut_of_neg {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed η)
    (lv centre : Site) (psi : Site → ℤ) {c : Site} (h : psi c < 0) :
    sheetOut P lv centre psi c = pointerOf (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData lv centre) c := by
  unfold sheetOut
  rw [if_neg (not_le.mpr h)]

/-- The phase policy at a centre with `Ψ < 0` is the `C`-policy. -/
theorem phasePolicy_of_neg {psi : Site → ℤ} {PA PC : Site → Site → Prop} {c : Site} (h : psi c < 0) :
    phasePolicy psi PA PC c = PC := by
  unfold phasePolicy
  exact if_neg (not_le.mpr h)

/-- `PhaseOK` at a `C`-centre: both signs negative, and the tie condition is vacuous. -/
theorem phaseOK_neg {psi : Site → ℤ} {c c' : Site} (hc : psi c < 0) (hc' : psi c' ≤ 0) : PhaseOK psi c c' := by
  refine ⟨fun h => absurd h (ne_of_lt hc), fun _ h2 => ?_⟩
  constructor
  · intro h3
    omega
  · intro h3
    omega

/-- The laplacian of the sheet `A` at a point with `Ψ ≥ 0` and `M`-laplacian `0` is the parent laplacian `0`. -/
theorem lapG_zero_of_nonneg {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {x : Site} (hx : 0 ≤ sheetPsi word x) (hM : laplacian (MW word) x = 0) :
    laplacian (standardField (conjWord word)) (zTurn (x - (frameAt word).sheetShift)) = 0 := by
  have hbinF : ∀ y, laplacian (FqW word) y = -1 ∨ laplacian (FqW word) y = 0 :=
    fun y => quarterTurnField_binary hSE.packet.binary y
  rw [← lap_sheetA word x]
  by_cases h1 : 1 ≤ sheetPsi word x
  · rw [← lap_MW_eq_sheetA hw hSE h1]
    exact hM
  · have h0 : sheetPsi word x = 0 := by omega
    have hT : (frameAt word).sheetC (FqW word) x = (frameAt word).sheetA (FqW word) x := by
      unfold sheetPsi at h0
      omega
    exact FLatticePaper.W1TieInputs.lapA_zero_of_mwhite (frameAt word) (FqW word) hbinF x hM hT

/-- A corner `p` of the parent square, reflected: its `M`-laplacian, and its reflected `C`-pointer in the reflected square. -/
theorem corner_C {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hfreeP : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquare P.retained (zTurn (c - (frameAt word).sheetShift)))
    {a b : ℤ} {p nx : Site} (hp : 0 ≤ sheetPsi word p) (hnx : Edge nx p)
    (hQ : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p nx)
    (hL : laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = -1 ∨
      (laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = 0 ∧
        ∀ j, sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p j → j = nx))
    (hnxS : nx ∈ squareCorners a b) :
    laplacian (MW word) ((frameAt word).centre - p) = -1 ∨
      (laplacian (MW word) ((frameAt word).centre - p) = 0 ∧
        sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) ((frameAt word).centre - p) ∈
          squareCorners ((frameAt word).centre.1 - a - 1) ((frameAt word).centre.2 - b - 1)) := by
  have hK : ((frameAt word).centre.1 + (frameAt word).centre.2) % 2 = 0 := (frameAt word).evenSite_centre
  have hF1 : sheetPsi word ((frameAt word).centre - p) = -sheetPsi word p := psi_reflect hw hSE p
  have hbinM : laplacian (MW word) p = -1 ∨ laplacian (MW word) p = 0 :=
    (FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong hw hSE).1 p
  rw [lap_MW_reflect hw hSE p]
  rcases hbinM with e | e
  · exact Or.inl e
  · refine Or.inr ⟨e, ?_⟩
    have hG0 := lapG_zero_of_nonneg hw hSE hp e
    rcases hL with e' | ⟨_, u⟩
    · rw [e'] at hG0
      norm_num at hG0
    · by_cases h1 : 1 ≤ sheetPsi word p
      · have hneg : sheetPsi word ((frameAt word).centre - p) < 0 := by omega
        rw [sheetOut_of_neg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hneg,
          pointerOf_sheetC_reflect P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre hK p nx hnx hQ u]
        exact (square_reflect (frameAt word).centre a b ((frameAt word).centre - nx)).2
          (by rw [sub_sub_cancel]; exact hnxS)
      · have h0 : sheetPsi word p = 0 := by omega
        have hx0 : 0 ≤ sheetPsi word ((frameAt word).centre - p) := by omega
        rw [sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hx0]
        have hT : (frameAt word).sheetC (FqW word) ((frameAt word).centre - p) =
            (frameAt word).sheetA (FqW word) ((frameAt word).centre - p) := by
          unfold sheetPsi at hF1 h0
          omega
        have hMx : laplacian (MW word) ((frameAt word).centre - p) = 0 := by
          rw [lap_MW_reflect hw hSE p]
          exact e
        have hH := FLatticePaper.W1MFinal.hagree_M_tie_of_inherited word hw hSE P hs hW1 hfreeP
          ((frameAt word).centre - p) hT hMx
        unfold FLatticePaper.W1MFinal.sheetQC at hH
        rw [sub_sub_cancel] at hH
        have hpt : (frameAt word).centre - pointerOf (sheetQ P.retained (frameAt word).sheetShift)
            ((frameAt word).centre - p) = nx :=
          u ((frameAt word).centre - pointerOf (sheetQ P.retained (frameAt word).sheetShift)
            ((frameAt word).centre - p)) hH
        have hptr : pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
            ((frameAt word).centre - p) = (frameAt word).centre - nx := by
          calc _ = (frameAt word).centre - ((frameAt word).centre -
                pointerOf (sheetQ P.retained (frameAt word).sheetShift) ((frameAt word).centre - p)) :=
                (sub_sub_cancel _ _).symm
            _ = (frameAt word).centre - nx := by rw [hpt]
        rw [hptr]
        exact (square_reflect (frameAt word).centre a b ((frameAt word).centre - nx)).2
          (by rw [sub_sub_cancel]; exact hnxS)

/-- A chain of relation `r` maps to a chain of `p` under a map that sends `r`-edges to `p`-edges. -/
theorem transGen_lift_map {α β : Type} {r : α → α → Prop} {p : β → β → Prop} (f : α → β)
    (h : ∀ x y, r x y → p (f x) (f y)) {x y : α} (hxy : Relation.TransGen r x y) :
    Relation.TransGen p (f x) (f y) := by
  induction hxy with
  | single hr => exact Relation.TransGen.single (h _ _ hr)
  | tail _ hr ih => exact Relation.TransGen.tail ih (h _ _ hr)

/-- **The `hsq` at a strict `C`-centre off the collar** (task 94). The `A`-square at `K − c` reflects to the square at `c`. -/
theorem hsq_C_offcollar {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hcoff : ¬ CollarFrame (frameAt word) c) (hc0 : sheetPsi word c < 0) (hM : laplacian (MW word) c = 0) :
    HsqAt word P c := by
  have hK : ((frameAt word).centre.1 + (frameAt word).centre.2) % 2 = 0 := (frameAt word).evenSite_centre
  have hF1 : sheetPsi word ((frameAt word).centre - c) = -sheetPsi word c := psi_reflect hw hSE c
  have hcs0 : 0 ≤ sheetPsi word ((frameAt word).centre - c) := by omega
  have hpos : 1 ≤ sheetPsi word ((frameAt word).centre - c) := by omega
  have hMs : laplacian (MW word) ((frameAt word).centre - c) = 0 := by
    rw [lap_MW_reflect hw hSE c]
    exact hM
  have hlz := lapG_zero_of_nonneg hw hSE hcs0 hMs
  have hpar : ParentSquareOut (standardField (conjWord word)) P.retained
      (zTurn ((frameAt word).centre - c - (frameAt word).sheetShift)) := by
    by_cases hnf : Nonfree (frameAt (conjWord word)) (zTurn ((frameAt word).centre - c - (frameAt word).sheetShift))
    · exact parentSquareOut_nonfree P.toOldPolicyWitness.toOldPolicyData hs hSE.packet hW1 hlz hnf
    · exact hfree _ hcs0 hMs hnf
  have hfreeP : ∀ c' : Site, (frameAt word).sheetC (FqW word) c' = (frameAt word).sheetA (FqW word) c' →
      laplacian (MW word) c' = 0 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c' - (frameAt word).sheetShift)) →
      ParentSquare P.retained (zTurn (c' - (frameAt word).sheetShift)) := by
    intro c' hT hM' hnf'
    have h0 : 0 ≤ sheetPsi word c' := by
      unfold sheetPsi
      omega
    exact parentSquare_of_out (hfree c' h0 hM' hnf')
  obtain ⟨p0, p1, p2, o', a, b, hcS', hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin0, hnot0, hE1, hE2, hE3,
    hR0, hR1, hR2, hoin, hoout, hRo, hun, hL0, hL1, hL2⟩ :=
    sheet_squareOut_of_parent (frameAt word).evenSite_sheetShift ((frameAt word).centre - c) hpar
  have hp0 : 0 ≤ sheetPsi word p0 :=
    psi_input_nonneg hw hSE (c := (frameAt word).centre - c) (j := p0) hin0 hpos
  have hp1 : 0 ≤ sheetPsi word p1 := by
    have := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p0) (q := p1) hR0
    omega
  have hp2 : 0 ≤ sheetPsi word p2 := by
    have := psi_mono hw hSE P.toOldPolicyWitness.toOldPolicyData (p := p1) (q := p2) hR1
    omega
  have hcC : c ∈ squareCorners ((frameAt word).centre.1 - a - 1) ((frameAt word).centre.2 - b - 1) :=
    (square_reflect (frameAt word).centre a b c).2 hcS'
  unfold HsqAt
  refine ⟨(frameAt word).centre.1 - a - 1, (frameAt word).centre.2 - b - 1, hcC, ?_, ?_, ?_, ?_⟩
  · have hopen : (frameAt word).openRect c := (FLatticePaper.W1Exit.openRect_iff (frameAt word) c).mpr hcS
    intro c' hc'
    obtain ⟨h1, h2⟩ := corner_close hcC hc'
    exact (FLatticePaper.W1Exit.openRect_iff (frameAt word) c').mp
      (strict_corners_of_not_collar (frameAt word) hn3 c hopen hcoff c' h1 h2)
  · have hsoC : sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c =
        (frameAt word).centre - o' := by
      rw [sheetOut_of_neg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hc0]
      have h := pointerOf_sheetC_reflect P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
        (frameAt word).centre hK ((frameAt word).centre - c) o' hoin hRo hun
      rw [sub_sub_cancel] at h
      exact h
    rw [hsoC]
    intro h
    have h' := (square_reflect (frameAt word).centre a b ((frameAt word).centre - o')).1 h
    rw [sub_sub_cancel] at h'
    exact hoout h'
  · intro x hx hne
    have hxS : (frameAt word).centre - x ∈ squareCorners a b := (square_reflect (frameAt word).centre a b x).1 hx
    have hne' : (frameAt word).centre - x ≠ (frameAt word).centre - c := fun e => hne (sub_right_inj.mp e)
    rcases hcov ((frameAt word).centre - x) hxS hne' with e | e | e
    · have hx' : x = (frameAt word).centre - p0 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp0 hE1 hR0 hL0 hq1
    · have hx' : x = (frameAt word).centre - p1 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp1 hE2 hR1 hL1 hq2
    · have hx' : x = (frameAt word).centre - p2 := by rw [← e, sub_sub_cancel]
      rw [hx']
      exact corner_C hw hSE P hs hW1 hfreeP hp2 hE3 hR2 hL2 hcS'
  · intro x hx hne _
    have hxS : (frameAt word).centre - x ∈ squareCorners a b := (square_reflect (frameAt word).centre a b x).1 hx
    have hne' : (frameAt word).centre - x ≠ (frameAt word).centre - c := fun e => hne (sub_right_inj.mp e)
    have T0 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p0
        ((frameAt word).centre - c) :=
      Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hR0) hR1) hR2
    have T1 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p1
        ((frameAt word).centre - c) :=
      Relation.TransGen.tail (Relation.TransGen.single hR1) hR2
    have T2 : Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift) p2
        ((frameAt word).centre - c) :=
      Relation.TransGen.single hR2
    rcases hcov ((frameAt word).centre - x) hxS hne' with e | e | e
    · have hx' : x = (frameAt word).centre - p0 := by rw [← e, sub_sub_cancel]
      have T0' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p0) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T0
      rw [sub_sub_cancel] at T0'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p0]; omega), T0'⟩
    · have hx' : x = (frameAt word).centre - p1 := by rw [← e, sub_sub_cancel]
      have T1' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p1) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T1
      rw [sub_sub_cancel] at T1'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p1]; omega), T1'⟩
    · have hx' : x = (frameAt word).centre - p2 := by rw [← e, sub_sub_cancel]
      have T2' : Relation.TransGen (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
          (frameAt word).centre) ((frameAt word).centre - p2) ((frameAt word).centre - ((frameAt word).centre - c)) :=
        transGen_lift_map (fun y => (frameAt word).centre - y)
          (fun u v huv => policyC_of_A P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
            (frameAt word).centre huv) T2
      rw [sub_sub_cancel] at T2'
      rw [hx', phasePolicy_of_neg hc0]
      exact ⟨phaseOK_neg hc0 (by rw [psi_reflect hw hSE p2]; omega), T2'⟩

/-- **The `hsq` at every strict centre with `M`-laplacian `0`** (task 94): the collar case and the free parent roots are named inputs,
and the off-collar case is `hsq_offcollar` (`Ψ ≥ 0`) or `hsq_C_offcollar` (`Ψ < 0`). -/
theorem hsq_all_of_inputs {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hcollar : ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → HsqAt word P c) :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → HsqAt word P c := by
  intro c hcS hM
  by_cases hcoll : CollarFrame (frameAt word) c
  · exact hcollar c hcS hM hcoll
  · by_cases hc0 : 0 ≤ sheetPsi word c
    · exact hsq_offcollar hw hSE P hs hW1 hn3 hfree hcS hcoll hc0 hM
    · exact hsq_C_offcollar hw hSE P hs hW1 hn3 hfree hcS hcoll (by omega) hM

/-- **W1Forced of the sheet minimum from the named inputs** (task 94): the collar and free-root inputs give `W1Forced` of `MW word`. -/
theorem W1Forced_of_inputs {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hcollar : ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → HsqAt word P c) :
    FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) :=
  FLatticePaper.W1Step.W1Forced_step word P (hsq_all_of_inputs hw hSE P hs hW1 hn3 hfree hcollar)

end FLatticePaper.W1NonfreeHsqC
