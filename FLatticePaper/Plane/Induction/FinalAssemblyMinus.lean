import FLatticePaper.Plane.Induction.FinalCoverMinus
import FLatticePaper.Plane.Induction.WordMinusRow
import FLatticePaper.Plane.Induction.WordDischarge
import FLatticePaper.Plane.Induction.FortPairMin
import FLatticePaper.Plane.Induction.FortAtRestricted
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.RowPair
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.KMinBridge
import FLatticePaper.Plane.Induction.RestrictedFortShift
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.PassageInv
import FLatticePaper.Plane.Induction.ForcedPriceSI
import FLatticePaper.Plane.Induction.FortAtRestricted
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # `RestrictedNoFort` for `permitsQ1` at sign `-1` on the easy words

Given a nonempty restricted fort in `{K ≥ level}`, the translate of `FortPairMin.exists_fort_translate_c0` has a minimum
point `r'` (price `cutPrice`, rounded slip `0`). The Q36 passage gives a point `f` of the translate in the closed polygon with
`kMinusW f = kMinusW r'` and `¬Nonfree f`: a free site `g = f + v` of the class of `f` with `v` in the deck span. The free site `g`
is a label of the minus row up to a period translate (`FinalCoverMinus`), so `f` is a row label `ℓ` up to the span; both have the
pair `(cutPrice, 0)`, so `lift_pair_unique` gives `f = ℓ`, which is outside the translate by the row results (`WordMinusRow`).

The named input `hcond` is the constant-pair claim of the passage (the K-minimal point of a restricted fort is in the closed
polygon, and the closed-polygon sites of minimal `kMinusW` have the pair `(cutPrice, 0)`). -/

namespace FLatticePaper.FinalAssemblyMinus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
  FLatticePaper.WordMinusEasy FLatticePaper.WordMinusRow FLatticePaper.WordDischarge FLatticePaper.FinalCoverMinus
  FLatticePaper.W1Seeds FLatticePaper.WordWebHyp FLatticePaper.WordVPattern FLatticePaper.FreeEnum FLatticePaper.KMinBridge

/-- `kMinusW` is the price plus the rounded slip for `η = -1`. -/
theorem kMinusW_eq (word : Word) (z : Site) :
    kMinusW word z = (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z := by
  unfold kMinusW jMinusW ChildFrame.roundedSlip ChildFrame.slip
  simp only [neg_one_smul]

/-- The length of the minus row. -/
theorem length_minusRow (r L d : ℤ) :
    (minusRow r L d).length = r.toNat + 2 + (d - 1).toNat + (L - r - 1).toNat := by
  unfold minusRow
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]


/-- **The pair `(cutPrice, 0)` on the closed polygon.** On the closed polygon `P ≤ cutPrice` (`StrongCore.priceRange`) and
`J_- ≤ 0` (`hsig_word`: `D_- ≤ 0`), so `K_- = cutPrice` forces `P = cutPrice` and `J_- = 0`. -/
theorem pair_of_kMinus_eq {word : Word} (hS : StrongCore word) {f : Site}
    (hf : f ∈ (frameAt word).closedPolygon) (hK : kMinusW word f = (frameAt word).cutPrice) :
    (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) (-1) f = 0 := by
  have hP := hS.priceRange f hf
  have hD := hsig_word hS f hf
  have hJ : (frameAt word).roundedSlip (standardField word) (-1) f ≤ 0 := by
    unfold ChildFrame.roundedSlip ChildFrame.slip
    simp only [neg_one_smul, ← sub_eq_add_neg] at *
    omega
  rw [kMinusW_eq] at hK
  constructor <;> omega

/-- **Every minus row site is outside a restricted fort of the word** (the list form of `WordMinusRow.minus_row_word`). -/
theorem minusSites_not_mem {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site}
    (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) (-1)) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z)
    (e : Site)
    (he : e ∈ MinusRowWiring.minusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) :
    e ∉ S := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  have hlen : k < (MinusRowWiring.minusSites (frameAt word)
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)).length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hlen' : k < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num).toNat + 2 +
      ((frameAt word).child.den - 1).toNat + ((frameAt word).child.den + (frameAt word).child.num -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1).toNat := by
    unfold MinusRowWiring.minusSites rowSites at hlen
    rw [List.length_map, length_minusRow] at hlen
    exact hlen
  exact minus_row_word hw hS hpar hSE hTrW hTrC hnd hres hK k e hlen' hk

/-- **A fort point in a free class is a minus row label.** If `f + v` is free (with `v` in the span) and `f` has the pair
`(cutPrice, 0)`, then `f` equals a minus row label, which has the same pair. -/
theorem fort_point_is_label {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hcut : FreeEnum.CutOnePerOrdinate (frameAt word))
    {f v : Site} (hv : v ∈ (frameAt word).child.modifiedDeck.span)
    (hg : f + v ∈ (frameAt word).freeH ∪ (frameAt word).freeV)
    (hf : (frameAt word).price (standardField word) f = (frameAt word).cutPrice ∧
      (frameAt word).roundedSlip (standardField word) (-1) f = 0) :
    ∃ ℓ ∈ MinusRowWiring.minusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
      f = ℓ := by
  obtain ⟨a, b, hab⟩ := span_eq_UV (frameAt word) hv
  have hper := hS.packet.periods
  have hd1 : (1 : ℤ) ≤ (frameAt word).child.den := by
    obtain ⟨hn0, hnd', -, hd3, -⟩ := (frameAt word).child_facts
    omega
  have hrL : (brk word) < FreeEnum.period (frameAt word) := by
    have := hrL2_word word
    unfold FreeEnum.period
    omega
  have hr0 : 0 ≤ brk word := (brk_pos word).le
  have hPU : ∀ z, (frameAt word).price (standardField word) (z + RowAt.Uvec (frameAt word)) =
      (frameAt word).price (standardField word) z + (-1) := fun z => RowPairWord.price_U _ _ hper z
  have hJU : ∀ z, (frameAt word).roundedSlip (standardField word) (-1) (z + RowAt.Uvec (frameAt word)) =
      (frameAt word).roundedSlip (standardField word) (-1) z := fun z => RowPairWord.roundedSlip_U _ _ hper z
  have hPV : ∀ z, (frameAt word).price (standardField word) (z + RowAt.Vvec (frameAt word)) =
      (frameAt word).price (standardField word) z := fun z => RowPairWord.price_V _ _ hper z
  have hJV : ∀ z, (frameAt word).roundedSlip (standardField word) (-1) (z + RowAt.Vvec (frameAt word)) =
      (frameAt word).roundedSlip (standardField word) (-1) z + (-1) := fun z => RowPairWord.roundedSlip_V _ _ hper z
  rcases hg with hH | hV
  · obtain ⟨j, hj, i, hi⟩ := freeH_cover (frameAt word) hH
    have hlab : FreeLabel.H j ∈ minusRow (brk word) (FreeEnum.period (frameAt word))
        ((frameAt word).child.den) := H_mem_minusRow _ _ _ j hd1 hj
    have hpair := RowPairWord.minusRow_pairs_word hw hSE hTrW hTrC (FreeLabel.H j) hlab
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
        (frameAt word).roundedSlip (standardField word) (-1)
          (RowAt.hAt (frameAt word) j + (i - a) • RowAt.Uvec (frameAt word) + (-b) • RowAt.Vvec (frameAt word)) = 0 := by
      rw [← hfeq]
      exact hf
    obtain ⟨hm, hn⟩ := RowPair.lift_pair_unique (frameAt word)
      (fun z => (frameAt word).price (standardField word) z)
      (fun z => (frameAt word).roundedSlip (standardField word) (-1) z) (frameAt word).cutPrice
      hPU hJU hPV hJV (RowAt.hAt (frameAt word) j) hpair (i - a) (-b) hg'
    refine ⟨RowAt.hAt (frameAt word) j, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨FreeLabel.H j, hlab, rfl⟩
    · rw [hfeq, hm, hn]
      simp
  · obtain ⟨k, hk, j, hj⟩ := freeV_cover (frameAt word) hcut hV (brk word) hr0 hrL
    have hlab : FreeLabel.V k ∈ minusRow (brk word) (FreeEnum.period (frameAt word))
        ((frameAt word).child.den) := V_mem_minusRow _ _ _ k hk
    have hpair := RowPairWord.minusRow_pairs_word hw hSE hTrW hTrC (FreeLabel.V k) hlab
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
        (frameAt word).roundedSlip (standardField word) (-1)
          (RowAt.vAt (frameAt word) k + (-a) • RowAt.Uvec (frameAt word) + (j - b) • RowAt.Vvec (frameAt word)) = 0 := by
      rw [← hfeq]
      exact hf
    obtain ⟨hm, hn⟩ := RowPair.lift_pair_unique (frameAt word)
      (fun z => (frameAt word).price (standardField word) z)
      (fun z => (frameAt word).roundedSlip (standardField word) (-1) z) (frameAt word).cutPrice
      hPU hJU hPV hJV (RowAt.vAt (frameAt word) k) hpair (-a) (j - b) hg'
    refine ⟨RowAt.vAt (frameAt word) k, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨FreeLabel.V k, hlab, rfl⟩
    · rw [hfeq, hm, hn]
      simp

/-- **`RestrictedNoFort` for `permitsQ1` at sign `-1`, at an easy word.** The named inputs are the Q36 passage inputs `hW`
(satisfiability) and `hW1` (the W1 forcing), and `hcond`, the constant-pair claim of the passage: the minimum point of a
restricted fort's translate lies in the closed polygon, and the closed-polygon sites of minimal `kMinusW` have the pair
`(cutPrice, 0)`. -/
theorem restrictedNoFort_minus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hz0 : ∀ (S' : Set Site) (r' : Site),
      IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) (-1)) S' →
      (∀ z ∈ S', (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) (-1) z) →
      r' ∈ S' → (frameAt word).price (standardField word) r' = (frameAt word).cutPrice →
      (frameAt word).roundedSlip (standardField word) (-1) r' = 0 →
      r' ∈ (frameAt word).closedPolygon) :
    RestrictedNoFort (standardField word)
      (fun z => (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) (-1) z)
      (permitsQ1 (frameAt word) (standardField word) (-1)) := by
  intro level S hne hres hlev
  have hper := hS.packet.periods
  have hPD : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) z + -1 ∧
      (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) z + 0 := by
    intro z
    have h1 := ChainDeck.price_kernel_mul (frameAt word) hS.packet 1 z
    have h2 := ChainDeck.price_transverse_mul (frameAt word) hS.packet 1 z
    rw [one_smul] at h1 h2
    exact ⟨by rw [h1]; ring, by rw [h2]; ring⟩
  have hSD : ∀ z, (frameAt word).slip (standardField word) (-1) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).slip (standardField word) (-1) z + 0 ∧
      (frameAt word).slip (standardField word) (-1) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).slip (standardField word) (-1) z + 2 * (-1) := by
    intro z
    exact ⟨by rw [ChildFrame.slip_kernel (frameAt word) (standardField word) hper (-1) z]; ring,
      ChildFrame.slip_transverse (frameAt word) (standardField word) hper (-1) z⟩
  have hL : ∀ (c : Site) (i j : ℤ), laplacian (standardField word)
      (c + (frameAt word).child.modifiedDeck.combine i j) = laplacian (standardField word) c :=
    fun c i j => laplacian_add_combine hper c i j
  obtain ⟨T, -, hres', ⟨r', hr'S, hr'p, hr's⟩, hK'⟩ :=
    FortPairMin.exists_fort_translate_c0 (frameAt word) (standardField word) (-1) (Or.inr rfl) hPD hSD hL hres hne
      level hlev
  have hmin : ∀ w ∈ RestrictedFortShift.shiftSet S T, kMinusW word r' ≤ kMinusW word w := by
    intro w hw'
    rw [kMinusW_eq, kMinusW_eq, hr'p, hr's]
    simpa using hK' w hw'
  have hfort := fortAt_nonfree_of_restricted (frameAt word) (standardField word) (-1) hres'
  have hcR := hz0 (RestrictedFortShift.shiftSet S T) r' hres' hK' hr'S hr'p hr's
  have hI0 : PassageInv.InvM word r' := by
    unfold PassageInv.InvM
    exact ⟨hr'p.le, hr's.le⟩
  obtain ⟨f, hfS, hfE, hfK, hfn, hfI⟩ := PassageInv.minus_passage_inv hw hSE (ForcedPriceSI.priceRangeOn_of_strong hS)
    hW hW1 hfort hr'S hcR hmin hI0
  have hpf := PassageInv.minus_pair_of_inv hfI (hfK.trans (by rw [kMinusW_eq, hr'p, hr's]; ring))
  have hex : ∃ v ∈ (frameAt word).child.modifiedDeck.span, f + v ∈ (frameAt word).freeH ∪ (frameAt word).freeV := by
    by_contra hcon
    exact hfn (fun v hv hmem => hcon ⟨v, hv, hmem⟩)
  obtain ⟨v, hv, hg⟩ := hex
  obtain ⟨ℓ, hℓ, hfℓ⟩ := fort_point_is_label hw hS hSE hTrW hTrC (CutOnePerProper.cutOnePerOrdinate_of_proper hw) hv hg hpf
  have hnot := minusSites_not_mem hw hS hpar hSE hTrW hTrC hnd hres' hK' ℓ hℓ
  exact hnot (hfℓ ▸ hfS)

end FLatticePaper.FinalAssemblyMinus
