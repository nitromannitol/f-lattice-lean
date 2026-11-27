import FLatticePaper.Plane.Induction.FinalCoverMinus
import FLatticePaper.Plane.Induction.PlusCover
import FLatticePaper.Plane.Induction.PlusRowPair
import FLatticePaper.Plane.Induction.PlusRowWiring
import FLatticePaper.Plane.Induction.WordPlusEasy
import FLatticePaper.Plane.Induction.WordDischarge
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.CutOnePerProper

/-! # The plus fort point is a plus row label (the covering and the lift for `eta = +1`) -/

namespace FLatticePaper.PlusFinal

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows FLatticePaper.FinalCoverMinus
  FLatticePaper.FreeEnum FLatticePaper.WordVPattern FLatticePaper.WordDischarge

/-- **The V covering.** A free V site is `vAt k + j V` for a label `V k` of the minus row (from `minus_row_covers`). -/
theorem freeV_cover_plus (frame : ChildFrame) (hcut : FreeEnum.CutOnePerOrdinate frame) {g : Site} (hg : g ∈ frame.freeV)
    (r : ℤ) (hr : 0 ≤ r) (hrL : r + 2 ≤ FreeEnum.period frame) :
    ∃ k : ℤ, k ∈ FreeCover.plusVIdx r (FreeEnum.period frame) ∧ ∃ j : ℤ, g = RowAt.vAt frame k + j • RowAt.Vvec frame := by
  obtain ⟨m, hm, rfl⟩ := VChain.freeV_eq_vpath_of_mem frame hg
  have hord : 0 ≤ (VChain.vpath frame m).2 ∧ (VChain.vpath frame m).2 < FreeEnum.period frame := by
    rw [VChain.vpath_ord]
    unfold FreeEnum.period
    constructor <;> omega
  have hbase : ∀ r' : ℤ, 0 ≤ r' → r' < FreeEnum.period frame →
      (fun x : ℤ => VChain.vpath frame x.toNat) r' ∈ frame.freeV ∧ ((fun x : ℤ => VChain.vpath frame x.toNat) r').2 = r' := by
    intro r' h0 h1
    refine ⟨ListPrefix.vpath_freeV_all frame r'.toNat (by unfold FreeEnum.period at h1; omega), ?_⟩
    rw [VChain.vpath_ord]
    omega
  obtain ⟨k, hk, n, hn⟩ := PlusCover.plus_row_covers frame hcut (fun x : ℤ => VChain.vpath frame x.toNat) hbase
    hg hord r hr hrL
  refine ⟨k, hk, n, ?_⟩
  have hv : RowAt.vAt frame k = FreeEnum.vAt frame (fun x : ℤ => VChain.vpath frame x.toNat) k := by
    unfold RowAt.vAt FreeEnum.vAt FreeEnum.period
    ext <;> simp [RowAt.Vvec, FLatticePaper.Induction.Vdeck]
  rw [hv, hn]
  ext <;> simp [RowAt.Vvec, FLatticePaper.Induction.Vdeck]


/-- **A fort point in a free class is a plus row label.** If `f + v` is free (with `v` in the span) and `f` has the pair
`(cutPrice, 0)`, then `f` equals a plus row label, which has the same pair. -/
theorem fort_point_is_label_plus {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hcut : FreeEnum.CutOnePerOrdinate (frameAt word))
    {f v : Site} (hv : v ∈ (frameAt word).child.modifiedDeck.span)
    (hg : f + v ∈ (frameAt word).freeH ∪ (frameAt word).freeV)
    (hf : (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) 1 f = 0) :
    ∃ ℓ ∈ PlusRowWiring.plusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
      f = ℓ := by
  obtain ⟨a, b, hab⟩ := span_eq_UV (frameAt word) hv
  have hper := hS.packet.periods
  have hd1 : (1 : ℤ) ≤ (frameAt word).child.den := by
    obtain ⟨hn0, hnd', -, hd3, -⟩ := (frameAt word).child_facts
    omega
  have hrL : (brk word) + 2 ≤ FreeEnum.period (frameAt word) := by
    have := hrL2_word word
    unfold FreeEnum.period
    omega
  have hr0 : 0 ≤ brk word := (brk_pos word).le
  have hPU : ∀ z, (frameAt word).price (standardField word) (z + RowAt.Uvec (frameAt word)) =
      (frameAt word).price (standardField word) z + (-1) := fun z => RowPairWord.price_U _ _ hper z
  have hJU : ∀ z, (frameAt word).roundedSlip (standardField word) 1 (z + RowAt.Uvec (frameAt word)) =
      (frameAt word).roundedSlip (standardField word) 1 z := fun z => PlusRowPair.roundedSlip_U_plus _ _ hper z
  have hPV : ∀ z, (frameAt word).price (standardField word) (z + RowAt.Vvec (frameAt word)) =
      (frameAt word).price (standardField word) z := fun z => RowPairWord.price_V _ _ hper z
  have hJV : ∀ z, (frameAt word).roundedSlip (standardField word) 1 (z + RowAt.Vvec (frameAt word)) =
      (frameAt word).roundedSlip (standardField word) 1 z + 1 := fun z => PlusRowPair.roundedSlip_V_plus _ _ hper z
  rcases hg with hH | hV
  · obtain ⟨j, hj, i, hi⟩ := freeH_cover (frameAt word) hH
    have hlab : FreeLabel.H j ∈ plusRow (brk word) (FreeEnum.period (frameAt word))
        ((frameAt word).child.den) := PlusCover.H_mem_plusRow _ _ _ j hd1 hj
    have hpair := PlusRowPair.plusRow_pairs_word hw hSE hTrW hTrC (FreeLabel.H j) hlab
    have hfeq : f = RowAt.hAt (frameAt word) j + (i - a) • RowAt.Uvec (frameAt word) +
        (-b) • RowAt.Vvec (frameAt word) := by
      have e1 := congrArg Prod.fst hi
      have e2 := congrArg Prod.snd hi
      have e3 := congrArg Prod.fst hab
      have e4 := congrArg Prod.snd hab
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2 e3 e4
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination e1 - e3
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination e2 - e4
    have hg' : (frameAt word).price (standardField word)
          (RowAt.hAt (frameAt word) j + (i - a) • RowAt.Uvec (frameAt word) + (-b) • RowAt.Vvec (frameAt word)) =
        (frameAt word).cutPrice ∧
        (frameAt word).roundedSlip (standardField word) 1
          (RowAt.hAt (frameAt word) j + (i - a) • RowAt.Uvec (frameAt word) + (-b) • RowAt.Vvec (frameAt word)) = 0 := by
      rw [← hfeq]
      exact hf
    obtain ⟨hm, hn⟩ := PlusRowPair.lift_pair_unique_gen (frameAt word) 1 (Or.inl rfl)
      (fun z => (frameAt word).price (standardField word) z)
      (fun z => (frameAt word).roundedSlip (standardField word) 1 z) (frameAt word).cutPrice
      hPU hJU hPV hJV (RowAt.hAt (frameAt word) j) hpair (i - a) (-b) hg'
    refine ⟨RowAt.hAt (frameAt word) j, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨FreeLabel.H j, hlab, rfl⟩
    · rw [hfeq, hm, hn]
      simp
  · obtain ⟨k, hk, j, hj⟩ := freeV_cover_plus (frameAt word) hcut hV (brk word) hr0 hrL
    have hlab : FreeLabel.V k ∈ plusRow (brk word) (FreeEnum.period (frameAt word))
        ((frameAt word).child.den) := PlusCover.V_mem_plusRow _ _ _ k hk
    have hpair := PlusRowPair.plusRow_pairs_word hw hSE hTrW hTrC (FreeLabel.V k) hlab
    have hfeq : f = RowAt.vAt (frameAt word) k + (-a) • RowAt.Uvec (frameAt word) +
        (j - b) • RowAt.Vvec (frameAt word) := by
      have e1 := congrArg Prod.fst hj
      have e2 := congrArg Prod.snd hj
      have e3 := congrArg Prod.fst hab
      have e4 := congrArg Prod.snd hab
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2 e3 e4
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination e1 - e3
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination e2 - e4
    have hg' : (frameAt word).price (standardField word)
          (RowAt.vAt (frameAt word) k + (-a) • RowAt.Uvec (frameAt word) + (j - b) • RowAt.Vvec (frameAt word)) =
        (frameAt word).cutPrice ∧
        (frameAt word).roundedSlip (standardField word) 1
          (RowAt.vAt (frameAt word) k + (-a) • RowAt.Uvec (frameAt word) + (j - b) • RowAt.Vvec (frameAt word)) = 0 := by
      rw [← hfeq]
      exact hf
    obtain ⟨hm, hn⟩ := PlusRowPair.lift_pair_unique_gen (frameAt word) 1 (Or.inl rfl)
      (fun z => (frameAt word).price (standardField word) z)
      (fun z => (frameAt word).roundedSlip (standardField word) 1 z) (frameAt word).cutPrice
      hPU hJU hPV hJV (RowAt.vAt (frameAt word) k) hpair (-a) (j - b) hg'
    refine ⟨RowAt.vAt (frameAt word) k, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨FreeLabel.V k, hlab, rfl⟩
    · rw [hfeq, hm, hn]
      simp


end FLatticePaper.PlusFinal
