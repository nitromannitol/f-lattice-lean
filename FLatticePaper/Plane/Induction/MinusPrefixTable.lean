import FLatticePaper.Plane.Induction.HardVFanBlocks
import FLatticePaper.Plane.Induction.FanExitCases
import FLatticePaper.Plane.Induction.FanExitBounds
import FLatticePaper.Plane.Induction.MinusRowWiring
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.HPaidInputs
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.RowAt

/-! # The exit table of the minus-prefix block (Q41 section 4, block 1)

For an even hard V entry `w = V_j` of the minus prefix (`1 ≤ j ≤ r`), every exit `u` of the rotated fan at `w` (a contacting input
outside the fan) is refuted from the earlier entries of the minus row or by a `lowPair`:
* a V-exit `Zs u = V_k` with `j < k ≤ r` is the earlier entry at position `r − k` of `minusSites` (`minusSites_V`);
* a V-exit with `r < k < L` is a `lowPair` (price `cutPrice`, rounded slip `−1`);
* an H-exit `Zs u = H + V − U` (`H` free H, `H ≠ (1,0)`) is a `lowPair`: its price is `price H + 1 ≤ cutPrice` (since `H ≠ hFirst`
  gives `price H < cutPrice`) and its rounded slip is `0 − 1 = −1`. -/

namespace FLatticePaper.MinusPrefixTable

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanRegion FLatticePaper.RefuteTree
  FLatticePaper.AuxRankQ1 FLatticePaper.RotatedCap FLatticePaper.RotatedForced FLatticePaper.MinusRowWiring FLatticePaper.CapRay
  FLatticePaper.FanPropagation FLatticePaper.HardVFanBlocks FLatticePaper.FreeRows

theorem minusSites_V (frame : ChildFrame) (r : ℤ) (i : ℕ) (hi : (i : ℤ) < r) :
    (minusSites frame r)[i]? = some (RowAt.vAt frame (r - (i : ℤ))) := by
  unfold minusSites rowSites
  rw [List.getElem?_map, minusRow_get_V _ _ _ i hi]
  simp [labelSite]

theorem zs_edge_of_input {q u : Site}
    (hu : (EvenSite q ∧ u = incomingPos q) ∨ (¬ EvenSite q ∧ Edge u q)) : Edge (Zs u) (Zs q) := by
  have hz := zs_inputs q
  rcases hu with ⟨-, rfl⟩ | ⟨-, hu⟩
  · rcases hz with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact Or.inr h2
    · exact Or.inl h2
  · rcases hu with rfl | rfl
    · rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases hz with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2

/-- **The exit table of the minus-prefix block.** -/
theorem minus_prefix_hexit (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hn3 : 3 ≤ frame.child.num)
    {r : ℤ} (j : ℕ) (hj1 : 1 ≤ j) (hjr : (j : ℤ) ≤ r)
    (hPH : ∀ h, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hJV : ∀ k : ℕ, r < (k : ℤ) → (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = -1)
    {N D : ℤ} (hN2 : 2 * N = frame.child.den - frame.child.num) (hD2 : 2 * D = frame.child.den + frame.child.num)
    (hN0 : 0 < N) (hND : N < D)
    (H : CapConeGrades.NLCap N D (quarterTurnField F))
    {w : Site} (hwj : w.2 = (j : ℤ)) (hw12 : 2 ≤ w.1 + w.2)
    (hb : N + 1 ≤ N * (w.2 + 1) - D * (-w.1))
    {K : ℕ} {p q : ℤ} (hK2 : 2 ≤ K) (hs : N * p - D * q = 1 - N) (hpq : (p + q) % 2 = 1)
    (hKs : 4 * N + 2 * D - 1 ≤ 2 * N * (K : ℤ)) (hKr : 2 * N * (K : ℤ) ≤ 3 * D + 5 * N - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ quarterTurnField F (p + (k : ℤ), q + (k : ℤ))) :
    ∀ q' : Site, q' ∈ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) (w.2 + 1, -w.1) K →
      ∀ u : Site, ((EvenSite q' ∧ u = incomingPos q') ∨ (¬ EvenSite q' ∧ Edge u q')) →
        quarterTurnField F u = parabolaField (-w.1) u →
        u ∉ fanSet (resRegion frame.child.num frame.child.den) (quarterTurnField F) (w.2 + 1, -w.1) K →
        Refuted frame F (-1) (earlierAt frame r (r - (j : ℤ)).toNat) (fun _ => False) (Zs u) := by
  intro q' hq u hu hc hnot
  have hqR : resRegion frame.child.num frame.child.den q' := hq.1.1
  have hqC : ConeRoot (w.2 + 1, -w.1) K q' := hq.1.2
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hon, hod⟩ := frame.child_odd
  have hn_eq : frame.child.num = D - N := by omega
  have hd_eq : frame.child.den = D + N := by omega
  -- the exit is not in the residual region (fan_next_NL)
  have hnotR : ¬ resRegion frame.child.num frame.child.den u := by
    intro hR
    have hopenU := resRegion_sub_ropen hn_eq hd_eq hN0 hND u hR
    have hopenQ := resRegion_sub_ropen hn_eq hd_eq hN0 hND q' hqR
    have hwu : u = incomingNeg q' ∨ u = incomingPos q' := by
      rcases hu with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr h
      · exact h
    have hev' : EvenSite q' → u = incomingPos q' := by
      intro he
      rcases hu with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd he hne
    have hcont : quarterTurnField F u = FLatticePaper.QuadraticCap.capMin (u.2 - (w.2 + 1, -w.1).2) := hc
    obtain ⟨-, hcone⟩ := CapConeGrades.fan_next_NL H hN0 hND le_rfl (by norm_num) hs hpq K hK2 hKs hKr hcap
      (w.2 + 1, -w.1) hb q' u ⟨hopenQ, hqC⟩ hwu hev' hopenU hcont
    exact hnot ⟨⟨hR, hcone⟩, hc⟩
  -- the exit bounds and the edge in the rotated rectangle
  obtain ⟨hz2, hsum⟩ := FanExitBounds.exit_bounds hw12 hqC hu
  have hUe : EvenSite (RowAt.Uvec frame) := by
    unfold EvenSite RowAt.Uvec
    simp only
    omega
  have hEdgeU : Edge (Zs u + RowAt.Uvec frame) (Zs q' + RowAt.Uvec frame) :=
    (AuxRankQ1.edge_shift hUe (Zs q') (Zs u)).mpr (zs_edge_of_input hu)
  have hopenZq : frame.openRect (Zs q' + RowAt.Uvec frame) :=
    (resRegion_eq_openRect frame q').mp hqR
  have hclosedU : Zs u + RowAt.Uvec frame ∈ frame.closedPolygon :=
    W1Exit.rectInputs frame _ hopenZq _ hEdgeU
  have hnotU : ¬ frame.openRect (Zs u + RowAt.Uvec frame) := fun h =>
    hnotR ((resRegion_eq_openRect frame u).mpr h)
  have hx0 : 0 ≤ (Zs u).2 := by omega
  rcases FanExitCases.fan_exit_class frame hn3 hx0 hsum hclosedU hnotU with ⟨hV, hVle⟩ | ⟨hH, hHne⟩
  · -- V-exit
    obtain ⟨k, hk, hkz⟩ := VChain.freeV_eq_vpath_of_mem frame hV
    have hk2 : (Zs u).2 = (k : ℤ) := by rw [hkz, VChain.vpath_ord frame k]
    rw [hkz]
    by_cases hkr : (k : ℤ) ≤ r
    · apply RefuteTree.Refuted.earlier
      refine ⟨(r - (k : ℤ)).toNat, by omega, ?_⟩
      rw [minusSites_V frame r (r - (k : ℤ)).toNat (by omega)]
      congr 1
      rw [← RowAt.vAt_nat frame k hk]
      congr 1
      omega
    · have hpr : frame.price F (VChain.vpath frame k) = frame.cutPrice :=
        PriceDeck.price_on_freeV frame F hP.strips (ListPrefix.vpath_freeV_all frame k hk)
      have hsl := hJV k (by omega) hk
      exact RefuteTree.Refuted.lowPair (by rw [hpr]) (by rw [hsl]; norm_num)
        (Or.inr (by rw [hsl]; norm_num))
  · -- H-exit: the exit is h + V - U with h a free H site, h ≠ (1,0)
    set h : Site := ((Zs u).1 + frame.child.den - (frame.child.num - frame.child.den),
      (Zs u).2 + frame.child.num - (frame.child.num + frame.child.den)) with hh
    have hHpr := hPH h hH
    have hneq : h ≠ FLatticePaper.Induction.hFirst := by
      intro e
      exact hHne (by rw [e]; rfl)
    have hpr_lt : frame.price F h ≠ frame.cutPrice := fun e => hneq (hHpr.2 e)
    have hcompat : Zs u + RowAt.Uvec frame = h + RowAt.Vvec frame := by
      unfold RowAt.Uvec RowAt.Vvec
      ext <;> simp [hh]
    have hpx : frame.price F (Zs u) = frame.price F h + 1 := by
      have e1 := RowPairWord.price_U frame F hP.periods (Zs u)
      have e2 : frame.price F (h + RowAt.Vvec frame) = frame.price F h := by
        unfold RowAt.Vvec
        exact HPaidInputs.price_V frame F hP h
      rw [← hcompat] at e2
      omega
    have hslip : frame.roundedSlip F (-1) (Zs u) = -1 := by
      have e1 := RowPairWord.roundedSlip_U frame F hP.periods (Zs u)
      have e2 := RowPairWord.roundedSlip_V frame F hP.periods h
      have e3 := hJH h hH
      rw [← hcompat] at e2
      omega
    exact RefuteTree.Refuted.lowPair (by omega) (by rw [hslip]; norm_num) (Or.inr (by rw [hslip]; norm_num))

end FLatticePaper.MinusPrefixTable
