import FLatticePaper.Plane.Induction.FreeSchedule
import FLatticePaper.Plane.Induction.BoundaryPair
import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.HPaidInputs
import FLatticePaper.Plane.Induction.WordBoundary

/-! # The prefix of the displayed lists: removal of the first entries and the core candidates

The minus list starts `V_r, …, V_1, H_0, V_0, …`: its entry at position `i < r` is `V_{r−i} = vAt (r − i)`. The plus list starts
`V_{−r−1}, …, V_{−2}, V_{−1}, H_0, …`: its entry at `i < r` is `vAt (−r−1+i)`. The first `r` entries of each list are removed in order
by the ordered-removal argument (`FreeSchedule.ordered_removal`), whose per-entry trichotomy `hforce` (componentwise lower site, earlier
entry, or fan start with its paid exit `hpaid`) is a named premise here. Each entry sits at the pair `(c₀, 0)`, so a lower site is excluded
by the minimum of `K`. The boundary set lemmas of `BoundaryPair` then give the core candidates. -/

namespace FLatticePaper.ListPrefix

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone

/-- **Prefix removal.** The entries `ent 0, …, ent (N−1)` at the pair `(c₀, 0)` are not in `S`, given the minimum of `K` on `S`, the
per-entry trichotomy `hforce`, the fan exits `hexit`, and the paid exits `hpaid`. -/
theorem prefix_removal (frame : ChildFrame) (F : Field) (S : Set Site) (P J : Site → ℤ) (c0 : ℤ)
    (ent : ℕ → Site) (N : ℕ)
    (hKmin : ∀ w ∈ S, c0 ≤ P w + J w)
    (hent : ∀ k < N, P (ent k) = c0 ∧ J (ent k) = 0)
    (hexit : ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → F v0 = parabolaField b.2 v0 →
      ∃ w : Site, w ∈ S ∧ F w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w)
    (hpaid : ∀ k < N, ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → F v0 = parabolaField b.2 v0 →
      ∀ w ∈ frame.closedPolygon, ¬ frame.openRect w → w ∈ S → F w = parabolaField b.2 w →
        ∃ j < k, ent j = w)
    (hforce : ∀ k < N, ent k ∈ S →
      (∃ w ∈ S, P w ≤ P (ent k) ∧ J w ≤ J (ent k) ∧ (P w < P (ent k) ∨ J w < J (ent k))) ∨
      (∃ j < k, ent j ∈ S) ∨
      (∃ v0 b : Site, v0 ∈ S ∧ frame.openRect v0 ∧ F v0 = parabolaField b.2 v0)) :
    ∀ k < N, ent k ∉ S := by
  refine FreeSchedule.ordered_removal S ent N ?_
  intro k hk hmem hIH
  rcases hforce k hk hmem with ⟨w, hwS, hwP, hwJ, hlt⟩ | ⟨j, hj, hjS⟩ | ⟨v0, b, hv0S, hv0o, hv0c⟩
  · have h1 := hKmin w hwS
    have h2 := hent k hk
    rcases hlt with hlt | hlt <;> linarith [h2.1, h2.2]
  · exact hIH j hj hjS
  · obtain ⟨w, hwS, hwc, hwcl, hwout⟩ := hexit v0 b hv0S hv0o hv0c
    obtain ⟨j, hj, hjw⟩ := hpaid k hk v0 b hv0S hv0o hv0c w hwcl hwout hwS hwc
    exact hIH j hj (by rw [hjw]; exact hwS)

/-- Every `vpath k` with `k < L` is a free V site. -/
theorem vpath_freeV_all (frame : ChildFrame) (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num) :
    VChain.vpath frame k ∈ frame.freeV := by
  by_cases h : (k : ℤ) < frame.child.den + frame.child.num - 1
  · exact VChain.vpath_free frame k h
  · have hk' : k = (frame.child.num + frame.child.den - 1).toNat := by omega
    rw [hk', ← VChain.vLast_eq_vpath]
    exact FLatticePaper.FreeVOrdinate.vLast_mem_freeV frame

/-- The minus entries `vAt j` (for `1 ≤ j ≤ r`) sit at the pair `(c₀, 0)`. -/
theorem minus_entry_pair (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ)
    (hrL : r ≤ frame.child.den + frame.child.num - 1)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (j : ℤ) (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    frame.price F (RowAt.vAt frame j) = frame.cutPrice ∧ frame.roundedSlip F (-1) (RowAt.vAt frame j) = 0 := by
  have hjL : j < frame.child.den + frame.child.num := by omega
  have hvj : RowAt.vAt frame j = VChain.vpath frame j.toNat := by
    have h := RowAt.vAt_nat frame j.toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h
    exact h
  rw [hvj]
  refine ⟨PriceDeck.price_on_freeV frame F hP.strips (vpath_freeV_all frame j.toNat (by omega)), ?_⟩
  rw [hpat j.toNat (by omega), if_pos (by omega)]

/-- **The minus core candidates.** On the minus domain `E`, with `K ≥ c₀` on `S` (the translated minimum), the removal of the first `r`
entries of the minus list leaves only `H_0` and `V_0` among the boundary sites of `S`. -/
theorem minus_hcand (frame : ChildFrame) (F G : Field) (hP : frame.Packet F) (r : ℤ)
    (hrL : r ≤ frame.child.den + frame.child.num - 1)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F (-1) w)
    (hexit : ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → G v0 = parabolaField b.2 v0 →
      ∃ w : Site, w ∈ S ∧ G w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w)
    (hpaid : ∀ k < r.toNat, ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → G v0 = parabolaField b.2 v0 →
      ∀ w ∈ frame.closedPolygon, ¬ frame.openRect w → w ∈ S → G w = parabolaField b.2 w →
        ∃ j < k, RowAt.vAt frame ((r - (j : ℤ))) = w)
    (hforce : ∀ k < r.toNat, RowAt.vAt frame (r - (k : ℤ)) ∈ S →
      (∃ w ∈ S, frame.price F w ≤ frame.price F (RowAt.vAt frame (r - (k : ℤ))) ∧
        frame.roundedSlip F (-1) w ≤ frame.roundedSlip F (-1) (RowAt.vAt frame (r - (k : ℤ))) ∧
        (frame.price F w < frame.price F (RowAt.vAt frame (r - (k : ℤ))) ∨
          frame.roundedSlip F (-1) w < frame.roundedSlip F (-1) (RowAt.vAt frame (r - (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt frame (r - (j : ℤ)) ∈ S) ∨
      (∃ v0 b : Site, v0 ∈ S ∧ frame.openRect v0 ∧ G v0 = parabolaField b.2 v0))
    (b : Site) (hbS : b ∈ S) (hbC : b ∈ frame.closedPolygon) (hbO : ¬ frame.openRect b) :
    b = FLatticePaper.Induction.hFirst ∨ b = FLatticePaper.Induction.vFirst := by
  have hK := hKmin b hbS
  rcases BoundaryPair.minus_boundary_K frame F hP r hPH hJH hpat b hbC hbO hK with hH | ⟨k, hkr, hkL, hbk⟩
  · exact Or.inl hH
  · by_cases hk0 : k = 0
    · right
      rw [hbk, hk0, VChain.vpath_zero]
    · exfalso
      have hrem := prefix_removal frame G S (fun w => frame.price F w) (fun w => frame.roundedSlip F (-1) w)
        frame.cutPrice (fun i : ℕ => RowAt.vAt frame (r - (i : ℤ))) r.toNat hKmin
        (fun i hi => minus_entry_pair frame F hP r hrL hpat (r - (i : ℤ)) (by omega) (by omega))
        hexit hpaid hforce
        ((r - (k : ℤ)).toNat) (by omega)
      apply hrem
      have e : r - (((r - (k : ℤ)).toNat : ℕ) : ℤ) = (k : ℤ) := by omega
      show RowAt.vAt frame (r - (((r - (k : ℤ)).toNat : ℕ) : ℤ)) ∈ S
      rw [e, RowAt.vAt_nat frame k (by omega), ← hbk]
      exact hbS

/-- The plus entries `vAt j` (for `−r − 1 ≤ j ≤ −2`) sit at the pair `(c₀, 0)`. -/
theorem plus_entry_pair (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (j : ℤ) (hj1 : -r - 1 ≤ j) (hj2 : j ≤ -2) :
    frame.price F (RowAt.vAt frame j) = frame.cutPrice ∧ frame.roundedSlip F 1 (RowAt.vAt frame j) = 0 := by
  have hL := RowAt.vAt_add_len frame j
  have hvjL : RowAt.vAt frame (j + (frame.child.den + frame.child.num)) =
      VChain.vpath frame (j + (frame.child.den + frame.child.num)).toNat := by
    have h := RowAt.vAt_nat frame (j + (frame.child.den + frame.child.num)).toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h
    exact h
  have hPe : frame.price F (RowAt.vAt frame (j + (frame.child.den + frame.child.num))) = frame.cutPrice := by
    rw [hvjL]
    exact PriceDeck.price_on_freeV frame F hP.strips
      (vpath_freeV_all frame _ (by omega))
  have hJe : frame.roundedSlip F 1 (RowAt.vAt frame (j + (frame.child.den + frame.child.num))) = 1 := by
    rw [hvjL, hpat _ (by omega), if_neg (by omega)]
  have hPV' : frame.price F (RowAt.vAt frame (j + (frame.child.den + frame.child.num))) =
      frame.price F (RowAt.vAt frame j) := by
    rw [hL]
    exact HPaidInputs.price_V frame F hP _
  have hJV' : frame.roundedSlip F 1 (RowAt.vAt frame (j + (frame.child.den + frame.child.num))) =
      frame.roundedSlip F 1 (RowAt.vAt frame j) + 1 := by
    rw [hL]
    exact HPaidInputs.roundedSlip_V frame F hP 1 _
  constructor
  · rw [← hPV']
    exact hPe
  · linarith

/-- **The plus core candidates.** On the plus domain `E − V` (the site `b` with `b + V` on the boundary of `E`), with `K ≥ c₀` on `S`,
the removal of the first `r` entries of the plus list leaves only `H_0` and `V_{−1} = vAt (−1)`. -/
theorem plus_hcand (frame : ChildFrame) (F G : Field) (hP : frame.Packet F) (r : ℤ)
    (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F 1 h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, frame.cutPrice ≤ frame.price F w + frame.roundedSlip F 1 w)
    (hexit : ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → G v0 = parabolaField b.2 v0 →
      ∃ w : Site, w ∈ S ∧ G w = parabolaField b.2 w ∧ w ∈ frame.closedPolygon ∧ ¬ frame.openRect w)
    (hpaid : ∀ k < r.toNat, ∀ v0 b : Site, v0 ∈ S → frame.openRect v0 → G v0 = parabolaField b.2 v0 →
      ∀ w ∈ frame.closedPolygon, ¬ frame.openRect w → w ∈ S → G w = parabolaField b.2 w →
        ∃ j < k, RowAt.vAt frame (-r - 1 + (j : ℤ)) = w)
    (hforce : ∀ k < r.toNat, RowAt.vAt frame (-r - 1 + (k : ℤ)) ∈ S →
      (∃ w ∈ S, frame.price F w ≤ frame.price F (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∧
        frame.roundedSlip F 1 w ≤ frame.roundedSlip F 1 (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∧
        (frame.price F w < frame.price F (RowAt.vAt frame (-r - 1 + (k : ℤ))) ∨
          frame.roundedSlip F 1 w < frame.roundedSlip F 1 (RowAt.vAt frame (-r - 1 + (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt frame (-r - 1 + (j : ℤ)) ∈ S) ∨
      (∃ v0 b : Site, v0 ∈ S ∧ frame.openRect v0 ∧ G v0 = parabolaField b.2 v0))
    (b : Site) (hbS : b ∈ S)
    (hw : (b.1 + (frame.child.num - frame.child.den), b.2 + (frame.child.num + frame.child.den)) ∈
      frame.closedPolygon)
    (hnot : ¬ frame.openRect (b.1 + (frame.child.num - frame.child.den), b.2 + (frame.child.num + frame.child.den))) :
    b = FLatticePaper.Induction.hFirst ∨ b = RowAt.vAt frame (-1) := by
  have hK := hKmin b hbS
  rcases BoundaryPair.plus_boundary_K frame F hP r hPH hJH hpat b hw hnot hK with hH | ⟨j, hj1, hj2, hbj⟩
  · exact Or.inl hH
  · by_cases hj : j = -1
    · right
      rw [hbj, hj]
    · exfalso
      have hrem := prefix_removal frame G S (fun w => frame.price F w) (fun w => frame.roundedSlip F 1 w)
        frame.cutPrice (fun i : ℕ => RowAt.vAt frame (-r - 1 + (i : ℤ))) r.toNat hKmin
        (fun i hi => plus_entry_pair frame F hP r hr2 hpat (-r - 1 + (i : ℤ)) (by omega) (by omega))
        hexit hpaid hforce
        ((j + r + 1).toNat) (by omega)
      apply hrem
      have e : -r - 1 + (((j + r + 1).toNat : ℕ) : ℤ) = j := by omega
      show RowAt.vAt frame (-r - 1 + (((j + r + 1).toNat : ℕ) : ℤ)) ∈ S
      rw [e, ← hbj]
      exact hbS

/-- **The minus core candidates at the game's word.** The pair is `(frameAt word, standardField word)`; `hPH` comes from the trace of the
word and `hJH` from its own zero strip. Named: the minimum of `K` on `S`, the fan exits, the paid exits, the per-entry trichotomy, and the V
pattern. -/
theorem minus_hcand_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW : StrongEstimates word) (hTr : TraceFromPsi.TraceAt word)
    (G : Field) (r : ℤ) (hrL : r ≤ (frameAt word).child.den + (frameAt word).child.num - 1)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ r then 0 else -1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) w +
      (frameAt word).roundedSlip (standardField word) (-1) w)
    (hexit : ∀ v0 b : Site, v0 ∈ S → (frameAt word).openRect v0 → G v0 = parabolaField b.2 v0 →
      ∃ w : Site, w ∈ S ∧ G w = parabolaField b.2 w ∧ w ∈ (frameAt word).closedPolygon ∧
        ¬ (frameAt word).openRect w)
    (hpaid : ∀ k < r.toNat, ∀ v0 b : Site, v0 ∈ S → (frameAt word).openRect v0 → G v0 = parabolaField b.2 v0 →
      ∀ w ∈ (frameAt word).closedPolygon, ¬ (frameAt word).openRect w → w ∈ S → G w = parabolaField b.2 w →
        ∃ j < k, RowAt.vAt (frameAt word) (r - (j : ℤ)) = w)
    (hforce : ∀ k < r.toNat, RowAt.vAt (frameAt word) (r - (k : ℤ)) ∈ S →
      (∃ w ∈ S, (frameAt word).price (standardField word) w ≤
          (frameAt word).price (standardField word) (RowAt.vAt (frameAt word) (r - (k : ℤ))) ∧
        (frameAt word).roundedSlip (standardField word) (-1) w ≤
          (frameAt word).roundedSlip (standardField word) (-1) (RowAt.vAt (frameAt word) (r - (k : ℤ))) ∧
        ((frameAt word).price (standardField word) w <
            (frameAt word).price (standardField word) (RowAt.vAt (frameAt word) (r - (k : ℤ))) ∨
          (frameAt word).roundedSlip (standardField word) (-1) w <
            (frameAt word).roundedSlip (standardField word) (-1) (RowAt.vAt (frameAt word) (r - (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt (frameAt word) (r - (j : ℤ)) ∈ S) ∨
      (∃ v0 b : Site, v0 ∈ S ∧ (frameAt word).openRect v0 ∧ G v0 = parabolaField b.2 v0))
    (b : Site) (hbS : b ∈ S) (hbC : b ∈ (frameAt word).closedPolygon) (hbO : ¬ (frameAt word).openRect b) :
    b = FLatticePaper.Induction.hFirst ∨ b = FLatticePaper.Induction.vFirst :=
  minus_hcand (frameAt word) (standardField word) G hW.packet r hrL (WordBoundary.hPH_of_trace hTr)
    (fun h hh => WordBoundary.roundedSlip_freeH_word hw hSE (η := -1) (by norm_num) hh) hpat S hKmin
    hexit hpaid hforce b hbS hbC hbO

/-- **The plus core candidates at the game's word.** On the domain `E − V`; `hPH` from the trace, `hJH` from the word's own zero strip
(`η = 1`). Named: the minimum of `K` on `S`, the fan exits, the paid exits, the per-entry trichotomy, and the V pattern. -/
theorem plus_hcand_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW : StrongEstimates word) (hTr : TraceFromPsi.TraceAt word)
    (G : Field) (r : ℤ) (hr2 : r ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) 1 (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - r - 2 then 0 else 1)
    (S : Set Site)
    (hKmin : ∀ w ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) w +
      (frameAt word).roundedSlip (standardField word) 1 w)
    (hexit : ∀ v0 b : Site, v0 ∈ S → (frameAt word).openRect v0 → G v0 = parabolaField b.2 v0 →
      ∃ w : Site, w ∈ S ∧ G w = parabolaField b.2 w ∧ w ∈ (frameAt word).closedPolygon ∧
        ¬ (frameAt word).openRect w)
    (hpaid : ∀ k < r.toNat, ∀ v0 b : Site, v0 ∈ S → (frameAt word).openRect v0 → G v0 = parabolaField b.2 v0 →
      ∀ w ∈ (frameAt word).closedPolygon, ¬ (frameAt word).openRect w → w ∈ S → G w = parabolaField b.2 w →
        ∃ j < k, RowAt.vAt (frameAt word) (-r - 1 + (j : ℤ)) = w)
    (hforce : ∀ k < r.toNat, RowAt.vAt (frameAt word) (-r - 1 + (k : ℤ)) ∈ S →
      (∃ w ∈ S, (frameAt word).price (standardField word) w ≤
          (frameAt word).price (standardField word) (RowAt.vAt (frameAt word) (-r - 1 + (k : ℤ))) ∧
        (frameAt word).roundedSlip (standardField word) 1 w ≤
          (frameAt word).roundedSlip (standardField word) 1 (RowAt.vAt (frameAt word) (-r - 1 + (k : ℤ))) ∧
        ((frameAt word).price (standardField word) w <
            (frameAt word).price (standardField word) (RowAt.vAt (frameAt word) (-r - 1 + (k : ℤ))) ∨
          (frameAt word).roundedSlip (standardField word) 1 w <
            (frameAt word).roundedSlip (standardField word) 1 (RowAt.vAt (frameAt word) (-r - 1 + (k : ℤ))))) ∨
      (∃ j < k, RowAt.vAt (frameAt word) (-r - 1 + (j : ℤ)) ∈ S) ∨
      (∃ v0 b : Site, v0 ∈ S ∧ (frameAt word).openRect v0 ∧ G v0 = parabolaField b.2 v0))
    (b : Site) (hbS : b ∈ S)
    (hw' : (b.1 + ((frameAt word).child.num - (frameAt word).child.den),
        b.2 + ((frameAt word).child.num + (frameAt word).child.den)) ∈ (frameAt word).closedPolygon)
    (hnot : ¬ (frameAt word).openRect (b.1 + ((frameAt word).child.num - (frameAt word).child.den),
        b.2 + ((frameAt word).child.num + (frameAt word).child.den))) :
    b = FLatticePaper.Induction.hFirst ∨ b = RowAt.vAt (frameAt word) (-1) :=
  plus_hcand (frameAt word) (standardField word) G hW.packet r hr2 (WordBoundary.hPH_of_trace hTr)
    (fun h hh => WordBoundary.roundedSlip_freeH_word hw hSE (η := 1) (by norm_num) hh) hpat S hKmin
    hexit hpaid hforce b hbS hw' hnot

end FLatticePaper.ListPrefix
