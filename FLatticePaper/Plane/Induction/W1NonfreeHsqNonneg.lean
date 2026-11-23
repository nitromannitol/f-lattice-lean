import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.W1NonfreeSquare
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1TieInputs
import FLatticePaper.Plane.Induction.W1CollarFrame
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.StrongPriceValues

/-! # Task 93: the `hsq` clause at strict centres with `Ψ c ≥ 0` (nonfree and tie parents), off the collar

For a strict centre `c` with `M`-white and `Ψ c ≥ 0`, the parent square at `zTurn (c − lv)` (`ParentSquareOut`, from the forced derivation at a
nonfree root, or a named free-root input) transports to the sheet square (`sheet_squareOut_of_parent`). Its corners have `Ψ ≥ 0`. At a tie
centre (`Ψ c = 0`) every corner ties (`inputs_tie_of_mwhite`, then monotonicity). Every corner's `M`-laplacian is `−1`, or `0` with the
`A`-pointer its square successor (`corner_nonneg`: strict corners by `lap_MW_eq_sheetA`, tie corners by `lapA_zero_of_mwhite`). The `A`-pointer
of `c` is the rejected input `o'`, outside the square. The strictness of the corners is `strict_corners_of_not_collar`. The collar case is
a named input. -/

namespace FLatticePaper.W1NonfreeHsqNonneg

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare
open FLatticePaper.W1NonfreeOut FLatticePaper.W1NonfreeSheet FLatticePaper.W1NonfreeHsq FLatticePaper.W1Step
open FLatticePaper.W1Pointers FLatticePaper.W1NonfreeSquare FLatticePaper.W1CollarFrame

/-- The parent square with its output at a nonfree white root (task 93, the copy of `parentSquare_nonfree`). -/
theorem parentSquareOut_nonfree {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed) (hs : seed = fun _ _ => False) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) {z : Site}
    (hz : laplacian G z = 0) (hnf : Nonfree frame z) :
    ParentSquareOut G P.retained z := by
  subst hs
  rcases P.quota.2 z hz with hr | hr
  · rcases nonfree_root_forced_nonfree P hP hW1 hnf hr with hb | hF
    · rw [hz] at hb
      norm_num at hb
    · exact parentSquareOut_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF
  · rcases nonfree_root_forced_nonfree P hP hW1 hnf hr with hb | hF
    · rw [hz] at hb
      norm_num at hb
    · exact parentSquareOut_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF

/-- The sheet output of a centre with `Ψ ≥ 0` is its `A`-pointer. -/
theorem sheetOut_of_nonneg {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv centre : Site) (psi : Site → ℤ) {c : Site} (h : 0 ≤ psi c) :
    sheetOut P lv centre psi c = pointerOf (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c := by
  unfold sheetOut
  rw [if_pos h]

/-- The phase policy at a centre with `Ψ ≥ 0` is the `A`-policy. -/
theorem phasePolicy_of_nonneg {psi : Site → ℤ} {PA PC : Site → Site → Prop} {c : Site} (h : 0 ≤ psi c) :
    phasePolicy psi PA PC c = PA := by
  unfold phasePolicy
  exact if_pos h

/-- `PhaseOK` from nonnegativity at the centre and at the corner, and the tie condition. -/
theorem phaseOK_of {psi : Site → ℤ} {c c' : Site} (hc : 0 ≤ psi c) (hc' : 0 ≤ psi c') (hz : psi c = 0 → psi c' = 0) :
    PhaseOK psi c c' :=
  ⟨hz, fun _ _ => ⟨fun _ => hc', fun _ => hc⟩⟩

/-- Two corners of one unit square are within Chebyshev distance one. -/
theorem corner_close {a b : ℤ} {c w : Site} (hc : c ∈ squareCorners a b) (hw : w ∈ squareCorners a b) :
    |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨w1, w2⟩ := w
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hc hw
  show |w1 - c1| ≤ 1 ∧ |w2 - c2| ≤ 1
  exact ⟨abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr ⟨by omega, by omega⟩⟩

/-- A corner `p` of the square with `Ψ p ≥ 0`: `M`-laplacian `−1`, or `0` with `A`-pointer its successor `nx`. -/
theorem corner_nonneg {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {p nx : Site} (hnx : Edge nx p) (hQ : sheetPolicyA P (frameAt word).sheetShift p nx)
    (hL : laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = -1 ∨
      (laplacian (standardField (conjWord word)) (zTurn (p - (frameAt word).sheetShift)) = 0 ∧
        ∀ j, sheetPolicyA P (frameAt word).sheetShift p j → j = nx))
    (hp : 0 ≤ sheetPsi word p) :
    laplacian (MW word) p = -1 ∨
      (laplacian (MW word) p = 0 ∧ pointerOf (sheetPolicyA P (frameAt word).sheetShift) p = nx) := by
  have hbin : ∀ z, laplacian (MW word) z = -1 ∨ laplacian (MW word) z = 0 :=
    fun z => (FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong hw hSE).1 z
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  rcases hbin p with e | e
  · exact Or.inl e
  · have hA : laplacian (fun z => (frameAt word).sheetA (FqW word) z) p = 0 := by
      by_cases h1 : 1 ≤ sheetPsi word p
      · rw [← lap_MW_eq_sheetA hw hSE h1]
        exact e
      · have h0 : sheetPsi word p = 0 := by omega
        have hT : (frameAt word).sheetC (FqW word) p = (frameAt word).sheetA (FqW word) p := by
          unfold sheetPsi at h0
          omega
        exact FLatticePaper.W1TieInputs.lapA_zero_of_mwhite (frameAt word) (FqW word) hbinF p e hT
    rw [lap_sheetA word p] at hA
    rcases hL with e' | ⟨_, u⟩
    · rw [e'] at hA
      norm_num at hA
    · exact Or.inr ⟨e, pointer_of_unique (sheetPolicyA P (frameAt word).sheetShift) p nx hnx hQ u⟩

/-- The square at a centre `c` with `Ψ c ≥ 0` and `M`-laplacian `0`: corners, nonnegativity, the tie condition, the corner clauses, the
rejected input, and the chain to the centre. -/
theorem square_nonneg {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (Pd : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    {c : Site} (hc0 : 0 ≤ sheetPsi word c) (hM : laplacian (MW word) c = 0)
    (hpar : ParentSquareOut (standardField (conjWord word)) Pd.retained (zTurn (c - (frameAt word).sheetShift))) :
    ∃ p0 p1 p2 o' : Site, ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      (0 ≤ sheetPsi word p0 ∧ 0 ≤ sheetPsi word p1 ∧ 0 ≤ sheetPsi word p2) ∧
      (sheetPsi word c = 0 → sheetPsi word p0 = 0 ∧ sheetPsi word p1 = 0 ∧ sheetPsi word p2 = 0) ∧
      (laplacian (MW word) p0 = -1 ∨
        (laplacian (MW word) p0 = 0 ∧ pointerOf (sheetPolicyA Pd (frameAt word).sheetShift) p0 = p1)) ∧
      (laplacian (MW word) p1 = -1 ∨
        (laplacian (MW word) p1 = 0 ∧ pointerOf (sheetPolicyA Pd (frameAt word).sheetShift) p1 = p2)) ∧
      (laplacian (MW word) p2 = -1 ∨
        (laplacian (MW word) p2 = 0 ∧ pointerOf (sheetPolicyA Pd (frameAt word).sheetShift) p2 = c)) ∧
      pointerOf (sheetPolicyA Pd (frameAt word).sheetShift) c = o' ∧ o' ∉ squareCorners a b ∧
      Relation.TransGen (sheetPolicyA Pd (frameAt word).sheetShift) p0 c ∧
      Relation.TransGen (sheetPolicyA Pd (frameAt word).sheetShift) p1 c ∧
      Relation.TransGen (sheetPolicyA Pd (frameAt word).sheetShift) p2 c := by
  have hlv := (frameAt word).evenSite_sheetShift
  obtain ⟨p0, p1, p2, o', a, b, hc_, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin0, hnot0, hE1, hE2, hE3,
    hR0, hR1, hR2, hoin, hoout, hRo, hun, hL0, hL1, hL2⟩ := sheet_squareOut_of_parent hlv c hpar
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hTie : sheetPsi word c = 0 → sheetPsi word p0 = 0 := by
    intro h0
    have hT : (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c := by
      unfold sheetPsi at h0
      omega
    have hi := FLatticePaper.W1TieInputs.inputs_tie_of_mwhite (frameAt word) (FqW word) hbinF c hM hT p0 hin0
    unfold sheetPsi
    omega
  have hp0 : 0 ≤ sheetPsi word p0 := by
    by_cases h1 : 1 ≤ sheetPsi word c
    · exact psi_input_nonneg hw hSE (c := c) (j := p0) hin0 h1
    · have h0 : sheetPsi word c = 0 := by omega
      have := hTie h0
      omega
  have hup1 : sheetPsi word p0 ≤ sheetPsi word p1 := psi_mono hw hSE Pd (p := p0) (q := p1) hR0
  have hup2 : sheetPsi word p1 ≤ sheetPsi word p2 := psi_mono hw hSE Pd (p := p1) (q := p2) hR1
  have hup3 : sheetPsi word p2 ≤ sheetPsi word c := psi_mono hw hSE Pd (p := p2) (q := c) hR2
  have hp1 : 0 ≤ sheetPsi word p1 := by omega
  have hp2 : 0 ≤ sheetPsi word p2 := by omega
  have hz : sheetPsi word c = 0 → sheetPsi word p0 = 0 ∧ sheetPsi word p1 = 0 ∧ sheetPsi word p2 = 0 := by
    intro h0
    have := hTie h0
    omega
  have k0 := corner_nonneg hw hSE Pd hE1 hR0 hL0 hp0
  have k1 := corner_nonneg hw hSE Pd hE2 hR1 hL1 hp1
  have k2 := corner_nonneg hw hSE Pd hE3 hR2 hL2 hp2
  refine ⟨p0, p1, p2, o', a, b, hc_, hq0, hq1, hq2, hcov, ⟨hp0, hp1, hp2⟩, hz, k0, k1, k2,
    pointer_of_unique (sheetPolicyA Pd (frameAt word).sheetShift) c o' hoin hRo hun, hoout, ?_, ?_, ?_⟩
  · exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hR0) hR1) hR2
  · exact Relation.TransGen.tail (Relation.TransGen.single hR1) hR2
  · exact Relation.TransGen.single hR2

/-- The `hsq` clause of `W1Step` at the centre `c`, as a predicate. -/
def HsqAt (word : Word) {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed) (c : Site) : Prop :=
  ∃ a b : ℤ,
    c ∈ squareCorners a b ∧
    (∀ c' ∈ squareCorners a b, StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
    sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c ∉ squareCorners a b ∧
    (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = -1 ∨
      (laplacian (MW word) c' = 0 ∧
        sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' ∈ squareCorners a b)) ∧
    (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian (MW word) c' = 0 →
      PhaseOK (sheetPsi word) c c' ∧
        Relation.TransGen (phasePolicy (sheetPsi word)
          (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
          (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c) c' c)

/-- **The off-collar `hsq` at a strict centre with `Ψ c ≥ 0`** (task 93). The parent square is `ParentSquareOut` at a nonfree root, or the
named free-root input `hfree`. -/
theorem hsq_offcollar {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    {c : Site} (hcS : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hcoff : ¬ CollarFrame (frameAt word) c) (hc0 : 0 ≤ sheetPsi word c) (hM : laplacian (MW word) c = 0) :
    HsqAt word P c := by
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hlz : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0 := by
    rw [← lap_sheetA word c]
    by_cases h1 : 1 ≤ sheetPsi word c
    · rw [← lap_MW_eq_sheetA hw hSE h1]
      exact hM
    · have h0 : sheetPsi word c = 0 := by omega
      have hT : (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c := by
        unfold sheetPsi at h0
        omega
      exact FLatticePaper.W1TieInputs.lapA_zero_of_mwhite (frameAt word) (FqW word) hbinF c hM hT
  have hpar : ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) := by
    by_cases hnf : Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift))
    · exact parentSquareOut_nonfree P.toOldPolicyWitness.toOldPolicyData hs hSE.packet hW1 hlz hnf
    · exact hfree c hc0 hM hnf
  obtain ⟨p0, p1, p2, o', a, b, hc_, hq0, hq1, hq2, hcov, hpos, hz, k0, k1, k2, hpo, hout, t0, t1, t2⟩ :=
    square_nonneg hw hSE P.toOldPolicyWitness.toOldPolicyData hc0 hM hpar
  unfold HsqAt
  refine ⟨a, b, hc_, ?_, ?_, ?_, ?_⟩
  · have hopen : (frameAt word).openRect c := (FLatticePaper.W1Exit.openRect_iff (frameAt word) c).mpr hcS
    intro c' hc'
    obtain ⟨h1, h2⟩ := corner_close hc_ hc'
    exact (FLatticePaper.W1Exit.openRect_iff (frameAt word) c').mp
      (strict_corners_of_not_collar (frameAt word) hn3 c hopen hcoff c' h1 h2)
  · rw [sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hc0, hpo]
    exact hout
  · intro c' hc' hne
    rcases hcov c' hc' hne with e | e | e
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.1]
      rcases k0 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hq1⟩
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.2.1]
      rcases k1 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hq2⟩
    · rw [e, sheetOut_of_nonneg P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) hpos.2.2]
      rcases k2 with h | ⟨h, hpt⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [hpt]; exact hc_⟩
  · intro c' hc' hne _
    rcases hcov c' hc' hne with e | e | e
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.1 (fun h0 => (hz h0).1), t0⟩
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.2.1 (fun h0 => (hz h0).2.1), t1⟩
    · rw [e, phasePolicy_of_nonneg hc0]
      exact ⟨phaseOK_of hc0 hpos.2.2 (fun h0 => (hz h0).2.2), t2⟩

/-- **The `hsq` at strict centres with `Ψ c ≥ 0`, with the collar case as a named input** (task 93). -/
theorem hsq_nonneg_of_inputs {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hfree : ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)))
    (hcollar : ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c → HsqAt word P c) :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → HsqAt word P c := by
  intro c hcS hM hc0
  by_cases hcoff : CollarFrame (frameAt word) c
  · exact hcollar c hcS hM hc0 hcoff
  · exact hsq_offcollar hw hSE P hs hW1 hn3 hfree hcS hcoff hc0 hM

end FLatticePaper.W1NonfreeHsqNonneg
