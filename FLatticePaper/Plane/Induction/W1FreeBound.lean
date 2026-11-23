import FLatticePaper.Plane.Induction.W1FreeHfree
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1TieBand
import FLatticePaper.Plane.Induction.W1TieInputs
import FLatticePaper.Plane.Induction.W1Inherited
import FLatticePaper.Plane.Induction.W1FreeDescent

/-! # Task 96: the rank bound on the sheet parent set, and the free table with the bound from the drift (the lead's (1))

The rank bound. The chain potential `Φ` drifts by `−1` along the kernel and `2η` along the transverse vector (`chainPotential_drift`), and
the rank `R` of the policy with increments `(−1, 2η)` (`rankIncr_two_of_ranked`) drifts by `−λ`, `2ηλ`. The quantity `R − λ(Φ − K)` is
invariant under those translations, so it is bounded by its values on finitely many representatives (`rank_bound_le`, the band argument of
`rank_bound_on_band` with `Φ ≤ K` in place of `Φ = K`). On the sheet parent set `Φ(zTurn(c − lv)) = K − Ψ c ≤ K` (`tie_iff_chain`, `Ψ c ≥ 0`),
so `R` is bounded there (`sheetParent_rank_bound`).

The descent uses this rank `R`, with `R` strictly decreasing along the retained edges (`free_forced_of_descent_rk`, the copy of
`free_forced_of_descent` with `P.rank` replaced by `R`), so the bound on the policy's own rank is not needed. -/

set_option linter.unusedSimpArgs false

namespace FLatticePaper.W1FreeBound

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare FLatticePaper.W1NonfreeOut
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1FreeHfree FLatticePaper.W1TieBand FLatticePaper.W1TieInputs
open FLatticePaper.W1ZeroPitch FLatticePaper.W1FreeDescent FLatticePaper.W1Step

/-- **The rank bound on a half-plane of the chain potential** (task 96, the band argument of `rank_bound_on_band` with `≤`). -/
theorem rank_bound_le {U V : Site} (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) {Φ R : Site → ℤ} {η lam K : ℤ} (hlam : 0 < lam)
    (hΦU : ∀ x, Φ (x + U) = Φ x - 1) (hΦV : ∀ x, Φ (x + V) = Φ x + 2 * η)
    (hRU : ∀ x, R (x + U) = R x - lam) (hRV : ∀ x, R (x + V) = R x + 2 * η * lam) :
    ∃ B : ℤ, ∀ x, Φ x ≤ K → R x ≤ B := by
  set D := U.1 * V.2 - U.2 * V.1 with hDdef
  have hΦ : ∀ (i j : ℤ) (w : Site), Φ (w + i • U + j • V) = Φ w - i + 2 * η * j := by
    intro i j w
    have h1 := shift_zsmul (f := Φ) (v := U) (c := -1) (fun z => by rw [hΦU z]; ring) i w
    have h2 := shift_zsmul (f := Φ) (v := V) (c := 2 * η) (fun z => by rw [hΦV z]) j (w + i • U)
    rw [h2, h1]
    ring
  have hR : ∀ (i j : ℤ) (w : Site), R (w + i • U + j • V) = R w + i * (-lam) + j * (2 * η * lam) := by
    intro i j w
    have h1 := shift_zsmul (f := R) (v := U) (c := -lam) (fun z => by rw [hRU z]; ring) i w
    have h2 := shift_zsmul (f := R) (v := V) (c := 2 * η * lam) (fun z => by rw [hRV z]) j (w + i • U)
    rw [h2, h1]
  have hD0 : D ≠ 0 := hD
  set box : Finset (ℤ × ℤ) := Finset.Icc (-|D|) |D| ×ˢ Finset.Icc (-|D|) |D| with hbox
  obtain ⟨B, hB⟩ := Finset.exists_le
    (box.image (fun p : ℤ × ℤ => R (p.1, p.2) - lam * (Φ (p.1, p.2) - K)))
  refine ⟨B, fun x htie => ?_⟩
  set w0 : Site := (x.1 % D, x.2 % D) with hw0
  have hw0box : w0 ∈ box := by
    have h1 := Int.emod_nonneg x.1 hD0
    have h2 := Int.emod_lt x.1 hD0
    have h3 := Int.emod_nonneg x.2 hD0
    have h4 := Int.emod_lt x.2 hD0
    rw [hbox]
    simp only [Finset.mem_product, Finset.mem_Icc, hw0]
    have hab := Int.abs_eq_natAbs D
    refine ⟨⟨by linarith [abs_nonneg D], by linarith⟩, ⟨by linarith [abs_nonneg D], by linarith⟩⟩
  set i : ℤ := x.1 / D * V.2 - x.2 / D * V.1 with hi
  set j : ℤ := -(x.1 / D) * U.2 + x.2 / D * U.1 with hj
  have hdec : x = w0 + i • U + j • V := by
    have e1 : x.1 % D = x.1 - D * (x.1 / D) := Int.emod_def x.1 D
    have e2 : x.2 % D = x.2 - D * (x.2 / D) := Int.emod_def x.2 D
    refine Prod.ext ?_ ?_
    · simp only [hw0, hi, hj, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      linear_combination (-1 : ℤ) * e1
    · simp only [hw0, hi, hj, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linear_combination (-1 : ℤ) * e2
  have hFx : R x - lam * (Φ x - K) = R w0 - lam * (Φ w0 - K) := by
    have h1 := hΦ i j w0
    have h2 := hR i j w0
    rw [← hdec] at h1 h2
    linear_combination h2 - lam * h1
  have hfin : R w0 - lam * (Φ w0 - K) ≤ B := hB _ (Finset.mem_image_of_mem _ hw0box)
  have hneg : lam * (Φ x - K) ≤ 0 := by nlinarith
  linarith

/-- **The rank of the policy bounded on the sheet parent set** (task 96): a rank `R`, strictly decreasing along the retained edges, bounded
above on `sheetParentSet word`. -/
theorem sheetParent_rank_bound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed) :
    ∃ R : Site → ℤ, (∀ c i : Site, P.retained c i → R i < R c) ∧ ∃ B : ℤ, ∀ x ∈ sheetParentSet word, R x ≤ B := by
  obtain ⟨K, hK⟩ := tie_iff_chain word h hSE.packet
  obtain ⟨r, lam, hlam, hstrict, hU, hV⟩ :=
    FLatticePaper.W1Inherited.rankIncr_two_of_ranked P (child_det_ne_zero (conjWord word)) hSE.priceDrift
      hSE.slipDrift (frameAt word).eps_unit
  have hRU : ∀ x : Site, r (x + (frameAt (conjWord word)).child.modifiedDeck.kernel) = r x - lam :=
    fun x => by linarith [hU x]
  have hRV : ∀ x : Site, r (x + (frameAt (conjWord word)).child.modifiedDeck.transverse) =
      r x + 2 * (frameAt word).eps * lam :=
    fun x => by linarith [hV x]
  obtain ⟨hΦU, hΦV⟩ := chainPotential_drift (frame := frameAt (conjWord word)) (G := standardField (conjWord word))
    (η := (frameAt word).eps) hSE.priceDrift (hSE.slipDrift _ (frameAt word).eps_unit)
  obtain ⟨B, hB⟩ := rank_bound_le (child_det_ne_zero (conjWord word)) (Φ := chainPot word (standardField (conjWord word)))
    (R := r) (η := (frameAt word).eps) (lam := lam) (K := K) hlam (fun x => hΦU x) (fun x => hΦV x) hRU hRV
  refine ⟨r, hstrict, B, ?_⟩
  rintro x ⟨c, h0, _, rfl⟩
  apply hB
  have hc : (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c +
      (frameAt (conjWord word)).chainPotential (standardField (conjWord word)) (frameAt word).eps
        (zTurn (c - (frameAt word).sheetShift)) = K := hK c
  have h0' : 0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) c -
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) c := h0
  unfold chainPot
  linarith

theorem free_forced_of_descent_rk {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked frame G seed) (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (S : Set Site) (B : ℤ) (Rk : Site → ℤ) (hdec : ∀ c i : Site, P.retained c i → Rk i < Rk c)
      (hB : ∀ x ∈ S, Rk x ≤ B)
    (hrow : ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
      z ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ z → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg z ∨ p0 = incomingPos z) ∧
      (p0 ∈ S ∧ p1 ∈ S ∧ p2 ∈ S) ∧
      Edge p1 p0 ∧ Edge p2 p1 ∧ Edge z p2 ∧
      P.retained p0 p1 ∧ P.retained p1 p2 ∧ P.retained p2 z) :
    ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 →
      ∃ o : Site, (o = incomingNeg z ∨ o = incomingPos z) ∧ ForcedEdge G (fun _ _ => False) z o := by
  have key : ∀ n : ℕ, ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → B - Rk z < n →
      ∃ o : Site, (o = incomingNeg z ∨ o = incomingPos z) ∧ ForcedEdge G (fun _ _ => False) z o := by
    intro n
    induction n with
    | zero =>
      intro z hz _ _ hlt
      have := hB z hz
      push_cast at hlt
      omega
    | succ n ih =>
      intro z hzS hfree hw hlt
      obtain ⟨p0, p1, p2, a, b, hzc, hp0c, hp1c, hp2c, hcov, hne01, hne12, hne02, hp0in, hSs, hE1, hE2, hE3,
        hR0, hR1, hR2⟩ := hrow z hzS hfree hw
      push_cast at hlt
      -- ranks increase along the chain towards the bottom: rank z < rank p2 < rank p1 < rank p0
      have hz2 : Rk z < Rk p2 := hdec p2 z hR2
      have hz1 : Rk z < Rk p1 := lt_trans hz2 (hdec p1 p2 hR1)
      have hz0 : Rk z < Rk p0 := lt_trans hz1 (hdec p0 p1 hR0)
      -- a white chain point is forced to its retained chain step
      have C : ∀ x y : Site, x ∈ S → P.retained x y → laplacian G x = 0 → B - Rk x < (n : ℤ) →
          ForcedEdge G (fun _ _ => False) x y := by
        intro x y hxS hr hxw hxlt
        by_cases hnf : Nonfree frame x
        · rcases nonfree_root_forced_nonfree P.toOldPolicyWitness.toOldPolicyData hP hW1 hnf hr with h | h
          · rw [hxw] at h
            norm_num at h
          · exact h
        · obtain ⟨o', _, hf⟩ := ih x hxS hnf hxw hxlt
          have heq := P.forcedWhiteUnique x y hr hxw o' hf
          rw [heq] at hf
          exact hf
      have hl0 : B - Rk p0 < (n : ℤ) := by omega
      have hl1 : B - Rk p1 < (n : ℤ) := by omega
      have hl2 : B - Rk p2 < (n : ℤ) := by omega
      -- the other input of z is outside the square
      set o : Site := if p0 = incomingNeg z then incomingPos z else incomingNeg z with ho_def
      have ho : o = incomingNeg z ∨ o = incomingPos z := by
        rw [ho_def]
        split_ifs <;> simp
      have hout : o ∉ squareCorners a b := other_input_outside hzc hp0c hp0in
      refine ⟨o, ho, ?_⟩
      refine ForcedEdge.unit (fun c' => if c' = p0 then p1 else if c' = p1 then p2 else z) hzc hw ho hout ?_ ?_
      · intro c' hc' hne
        rcases hcov c' hc' hne with h | h | h
        · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p1 := if_pos h
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hp1c
            · rw [h]
              exact hE1
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne01 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p2 := by
            rw [if_neg hne', if_pos h]
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hp2c
            · rw [h]
              exact hE2
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne02 e.symm
          have hne'' : c' ≠ p1 := by
            rw [h]
            exact fun e => hne12 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = z := by
            rw [if_neg hne', if_neg hne'']
          rw [hi]
          rcases hP.binary c' with hb | hb
          · exact Or.inl hb
          · refine Or.inr ⟨hb, ?_, ?_⟩
            · exact hzc
            · rw [h]
              exact hE3
      · intro c' hc' hne hwc'
        rcases hcov c' hc' hne with h | h | h
        · have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p1 := if_pos h
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p0 p1 hSs.1 hR0 hwc' hl0
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne01 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = p2 := by
            rw [if_neg hne', if_pos h]
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p1 p2 hSs.2.1 hR1 hwc' hl1
        · have hne' : c' ≠ p0 := by
            rw [h]
            exact fun e => hne02 e.symm
          have hne'' : c' ≠ p1 := by
            rw [h]
            exact fun e => hne12 e.symm
          have hi : (if c' = p0 then p1 else if c' = p1 then p2 else z) = z := by
            rw [if_neg hne', if_neg hne'']
          rw [hi]
          rw [h] at hwc' ⊢
          exact C p2 z hSs.2.2 hR2 hwc' hl2
  intro z hz hfree hw
  have h0 : 0 ≤ B - Rk z := by
    have := hB z hz
    omega
  have hcast : ((B - Rk z).toNat : ℤ) = B - Rk z := Int.toNat_of_nonneg h0
  exact key ((B - Rk z).toNat + 1) z hz hfree hw (by push_cast; omega)

/-- The parent square with output at a free white root of a set with a bounded rank `Rk` (the copy of `parentSquareOut_of_table`). -/
theorem parentSquareOut_of_table_rk {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked frame G seed) (hs : seed = fun _ _ => False)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (S : Set Site) (B : ℤ) (Rk : Site → ℤ) (hdec : ∀ c i : Site, P.retained c i → Rk i < Rk c)
    (hB : ∀ x ∈ S, Rk x ≤ B)
    (hTab : ∀ z ∈ S, ¬ Nonfree frame z → laplacian G z = 0 → TableShape P.retained S z)
    {z : Site} (hz : z ∈ S) (hnf : ¬ Nonfree frame z) (hw : laplacian G z = 0) :
    ParentSquareOut G P.retained z := by
  obtain ⟨o, -, hF⟩ := free_forced_of_descent_rk P hP hW1 S B Rk hdec hB
    (fun z' hz' hnf' hw' => rowSq_of_tableShape (hTab z' hz' hnf' hw')) z hz hnf hw
  subst hs
  exact parentSquareOut_of_forced P.quota P.forcedRetained P.forcedWhiteUnique hF

/-- **The lead's `hfree` on the sheet, with the rank bound from the drift** (task 96): the table is the only named input. -/
theorem hfree_sheet_rk {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hTab : ∀ z ∈ sheetParentSet word, ¬ Nonfree (frameAt (conjWord word)) z →
      laplacian (standardField (conjWord word)) z = 0 → TableShape P.retained (sheetParentSet word) z) :
    ∀ c : Site, 0 ≤ sheetPsi word c → laplacian (MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) := by
  obtain ⟨R, hdec, B, hB⟩ := sheetParent_rank_bound hw hSE P
  intro c h0 hM hnf
  exact parentSquareOut_of_table_rk P hs hSE.packet hW1 (sheetParentSet word) B R hdec hB hTab ⟨c, h0, hM, rfl⟩ hnf
    (FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE h0 hM)

/-- **W1Forced of the sheet minimum from the table and the collar input** (task 96): the rank bound is now derived, not named. -/
theorem W1Forced_of_tables_rk {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hTab : ∀ z ∈ sheetParentSet word, ¬ Nonfree (frameAt (conjWord word)) z →
      laplacian (standardField (conjWord word)) z = 0 → TableShape P.retained (sheetParentSet word) z)
    (hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
      HsqAt word P c) :
    FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (MW word) :=
  FLatticePaper.W1NonfreeHsqC.W1Forced_of_inputs hw hSE P hs hW1 hn3
    (hfree_sheet_rk hw hSE P hs hW1 hTab) hcollar

end FLatticePaper.W1FreeBound
