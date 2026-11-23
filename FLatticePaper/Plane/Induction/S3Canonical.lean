import FLatticePaper.Plane.Induction.S3NoFort
import FLatticePaper.Plane.Induction.SignedPolicy
import FLatticePaper.Plane.Induction.ParentStepDischarge

/-! Task 57: the S3 orders and the endpoint gate from the canonical signed policy (fix Q1, last part).

The canonical policy is the selected graph of the raw-slip game: `policy c i` retains the input `i` of the centre `c`.
With `P = cutGrade F 1 0 1` (the primitive price) and `J = cutGrade F 0 1 1` (the rounded slip), the selected graph satisfies:

* quota: black keeps both inputs, white keeps at least one (`RetainQuota`), and the kept inputs are permitted;
* `P` and `J` do not increase along kept inputs;
* a strict rank `R` decreases along kept inputs.

The natural orders of `S3NoFortInputs` are the same-pair counts `b(z) = #{u : (P, J)(u) = (P, J)(z), R(u) < R(z)}`. They are
finite: the period increments `(−1, 0)` and `(0, 1)` of `(P, J)` allow one lift of each pair per deck class, and the classes
are finite. A kept input with the same pair has a strictly smaller count. The gate follows selected inputs inside the
restricted fort: a strict componentwise drop ends it, a constant pair continues it (strict descent of `b`), and a free
endpoint has a smaller count. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The canonical signed policy of the raw-slip game of S3 (Q1): the selected inputs, the free set, and the strict rank. -/
structure CanonicalPolicy (frame : ChildFrame) (F : Field) (η : ℤ) where
  /-- `policy c i`: the input `i` of the centre `c` is selected. -/
  policy : Site → Site → Prop
  /-- The deck-invariant free set (the H/V boundary). -/
  free : Site → Prop
  freeInvariant : ∀ step ∈ frame.child.modifiedDeck.span, ∀ site, free (site + step) ↔ free site
  /-- Quota: black keeps both inputs, white keeps at least one. -/
  quota : RetainQuota F policy
  /-- Selected inputs are permitted in the raw-slip game. -/
  permitted : ∀ c i, policy c i → slipPermits F (fun z => F (z + η • frame.shortShift)) c i
  /-- The primitive price `P` does not increase along selected inputs. -/
  nonincreasingP : ∀ c i, policy c i → frame.cutGrade F 1 0 1 i ≤ frame.cutGrade F 1 0 1 c
  /-- The rounded slip `J` does not increase along selected inputs. -/
  nonincreasingJ : ∀ c i, policy c i → frame.cutGrade F 0 1 1 i ≤ frame.cutGrade F 0 1 1 c
  /-- The strict rank: it decreases along selected inputs with the same pair `(P, J)` (the only case the orders need). -/
  rank : Site → ℤ
  strictRank : ∀ c i, policy c i → frame.cutGrade F 1 0 1 i = frame.cutGrade F 1 0 1 c →
    frame.cutGrade F 0 1 1 i = frame.cutGrade F 0 1 1 c → rank i < rank c
  /-- At a free white the selected input is the prescribed signed H/V direction. -/
  freePrescribed : ∀ c, free c → laplacian F c = 0 →
    ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ ∀ j, policy c j ↔ j = i

namespace ChildFrame

variable (frame : ChildFrame)

theorem periodDenominator_eq_expr :
    frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
  unfold Fraction.periodDenominator
  ring

theorem combine_coords (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  unfold PeriodDeck.combine
  rw [frame.kernel_coords, frame.child_modifiedDeck_transverse]

theorem tGrade_add_deck (z : Site) (i j : ℤ) :
    frame.tGrade (z + frame.child.modifiedDeck.combine i j) =
      frame.tGrade z - j * frame.child.periodDenominator := by
  rw [frame.combine_coords, frame.periodDenominator_eq_expr]
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem sGrade_add_deck (z : Site) (i j : ℤ) :
    frame.sGrade (z + frame.child.modifiedDeck.combine i j) =
      frame.sGrade z + i * frame.child.periodDenominator := by
  rw [frame.combine_coords, frame.periodDenominator_eq_expr]
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem combine_sub (i j i' j' : ℤ) :
    frame.child.modifiedDeck.combine i j - frame.child.modifiedDeck.combine i' j' =
      frame.child.modifiedDeck.combine (i - i') (j - j') := by
  rw [frame.combine_coords, frame.combine_coords, frame.combine_coords]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub]
    ring
  · simp only [Prod.snd_sub]
    ring

theorem combine_zero : frame.child.modifiedDeck.combine 0 0 = 0 := by
  rw [frame.combine_coords]
  simp

theorem combine_parity (z : Site) (i j : ℤ) :
    EvenSite (z + frame.child.modifiedDeck.combine i j) ↔ EvenSite z := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.child.num + frame.child.den = 2 * m := ⟨(frame.child.num + frame.child.den) / 2, by
    omega⟩
  unfold EvenSite
  rw [frame.combine_coords]
  simp only [Prod.fst_add, Prod.snd_add]
  have e : z.1 + (i * frame.child.den + j * (frame.child.num - frame.child.den)) +
      (z.2 + (i * frame.child.num + j * (frame.child.num + frame.child.den))) =
      (z.1 + z.2) + 2 * (m * i + frame.child.num * j) := by
    linear_combination i * hm
  rw [e]
  generalize m * i + frame.child.num * j = X
  omega

/-- Every site is a deck shift of a site of the closed polygon. -/
theorem exists_shift_mem (u : Site) :
    ∃ i j : ℤ, u + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon := by
  have hT : 0 < frame.child.periodDenominator := by
    obtain ⟨hnpos, hnd, -, -, -⟩ := frame.child_facts
    rw [frame.periodDenominator_eq_expr]
    nlinarith
  obtain ⟨hnpos, hnd, hdiff, hd3, -⟩ := frame.child_facts
  have hev := frame.child_even
  by_cases hu : EvenSite u
  · obtain ⟨j, hj1, hj2⟩ := exists_box_shift (frame.tGrade u) (2 - frame.child.periodDenominator)
      frame.child.periodDenominator hT
    obtain ⟨i, hi1, hi2⟩ := exists_box_shift (frame.sGrade u) 0 frame.child.periodDenominator hT
    refine ⟨-i, j, ?_⟩
    rw [frame.mem_closedPolygon_iff]
    refine Or.inl ⟨(frame.combine_parity u (-i) j).mpr hu, ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_deck]
      linarith
    · rw [frame.tGrade_add_deck]
      linarith
    · rw [frame.sGrade_add_deck]
      linarith
    · rw [frame.sGrade_add_deck]
      linarith
  · obtain ⟨j, hj1, hj2⟩ := exists_box_shift (frame.tGrade u)
      (frame.child.num - frame.child.periodDenominator) frame.child.periodDenominator hT
    obtain ⟨i, hi1, hi2⟩ := exists_box_shift (frame.sGrade u)
      (2 - frame.child.den + frame.child.num) frame.child.periodDenominator hT
    refine ⟨-i, j, ?_⟩
    rw [frame.mem_closedPolygon_iff]
    refine Or.inr ⟨fun h => hu ((frame.combine_parity u (-i) j).mp h), ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_deck]
      linarith
    · rw [frame.tGrade_add_deck]
      linarith
    · rw [frame.sGrade_add_deck]
      linarith
    · rw [frame.sGrade_add_deck]
      linarith

/-- The closed polygon is finite: its grades `(t, s)` lie in a box and determine the site. -/
theorem closedPolygon_finite : frame.closedPolygon.Finite := by
  have hT : 0 < frame.child.periodDenominator := by
    obtain ⟨hnpos, hnd, -, -, -⟩ := frame.child_facts
    rw [frame.periodDenominator_eq_expr]
    nlinarith
  have hinj : Set.InjOn (fun z : Site => (frame.tGrade z, frame.sGrade z)) (Set.univ : Set Site) := by
    intro z _ z' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨ht, hs⟩ := h
    have hx : frame.child.periodDenominator * (z.1 - z'.1) = 0 := by
      rw [frame.periodDenominator_eq_expr]
      unfold ChildFrame.sGrade at hs
      unfold ChildFrame.tGrade at ht
      linear_combination (frame.child.den) * hs + (frame.child.den - frame.child.num) * ht
    have hy : frame.child.periodDenominator * (z.2 - z'.2) = 0 := by
      rw [frame.periodDenominator_eq_expr]
      unfold ChildFrame.sGrade at hs
      unfold ChildFrame.tGrade at ht
      linear_combination frame.child.num * hs - (frame.child.den + frame.child.num) * ht
    have hx' : z.1 - z'.1 = 0 := (mul_eq_zero.mp hx).resolve_left hT.ne'
    have hy' : z.2 - z'.2 = 0 := (mul_eq_zero.mp hy).resolve_left hT.ne'
    exact Prod.ext (by omega) (by omega)
  have hbox : ({p : ℤ × ℤ | p.1 ∈ Set.Icc (-frame.child.periodDenominator) (frame.child.den + frame.child.num) ∧
      p.2 ∈ Set.Icc (-(frame.child.den + frame.child.num)) (frame.child.periodDenominator + frame.child.den + frame.child.num)} :
      Set (ℤ × ℤ)).Finite := by
    have h1 : ((Set.Icc (-frame.child.periodDenominator) (frame.child.den + frame.child.num)) ×ˢ
        (Set.Icc (-(frame.child.den + frame.child.num)) (frame.child.periodDenominator + frame.child.den + frame.child.num)) :
        Set (ℤ × ℤ)).Finite :=
      (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
    exact h1
  have hsub : frame.closedPolygon ⊆
      (fun z : Site => (frame.tGrade z, frame.sGrade z)) ⁻¹'
        ({p : ℤ × ℤ | p.1 ∈ Set.Icc (-frame.child.periodDenominator) (frame.child.den + frame.child.num) ∧
          p.2 ∈ Set.Icc (-(frame.child.den + frame.child.num)) (frame.child.periodDenominator + frame.child.den + frame.child.num)} :
          Set (ℤ × ℤ)) := by
    intro z hz
    rw [Set.mem_preimage]
    rw [frame.mem_closedPolygon_iff] at hz
    have hT2 := frame.periodDenominator_eq_expr
    obtain ⟨hnpos, hnd, hdiff, hd3, -⟩ := frame.child_facts
    rcases hz with ⟨he, h⟩ | ⟨ho, h⟩
    · obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  exact Set.Finite.subset (hbox.preimage (hinj.mono (Set.subset_univ _))) hsub

end ChildFrame

section PairClasses

variable {frame : ChildFrame} {F : Field}

/-- The pair class of a pair `(p, q)`: the sites with `P = p` and `J = q`. -/
def pairClass (frame : ChildFrame) (F : Field) (p q : ℤ) : Set Site :=
  {u | frame.cutGrade F 1 0 1 u = p ∧ frame.cutGrade F 0 1 1 u = q}

/-- Each pair class is finite: each deck class carries at most one site of a given pair. -/
theorem pairClass_finite {cU cV : ℤ} (hper : HasGeneratorPeriods frame.child F cU cV) (p q : ℤ) :
    (pairClass frame F p q).Finite := by
  -- a representative of each site in the closed polygon, by a deck shift
  choose I J hIJ using fun u : Site => frame.exists_shift_mem u
  have hinjOn : Set.InjOn (fun u : Site => u + frame.child.modifiedDeck.combine (I u) (J u)) (pairClass frame F p q) := by
    intro u hu u' hu' h
    obtain ⟨hPu, hJu⟩ := hu
    obtain ⟨hPu', hJu'⟩ := hu'
    simp only at h
    have hdiff : u' = u + frame.child.modifiedDeck.combine (I u - I u') (J u - J u') := by
      rw [← frame.combine_sub]
      calc u' = (u' + frame.child.modifiedDeck.combine (I u') (J u')) -
            frame.child.modifiedDeck.combine (I u') (J u') := by abel
        _ = (u + frame.child.modifiedDeck.combine (I u) (J u)) -
            frame.child.modifiedDeck.combine (I u') (J u') := by rw [h]
        _ = u + (frame.child.modifiedDeck.combine (I u) (J u) -
            frame.child.modifiedDeck.combine (I u') (J u')) := by abel
    have hP' := frame.cutGrade_add_combine F hper 1 0 1 (I u - I u') (J u - J u') u
    have hJ' := frame.cutGrade_add_combine F hper 0 1 1 (I u - I u') (J u - J u') u
    rw [← hdiff, hPu'] at hP'
    rw [← hdiff, hJu'] at hJ'
    have ha : I u - I u' = 0 := by linarith
    have hb : J u - J u' = 0 := by nlinarith
    rw [hdiff, ha, hb, frame.combine_zero]
    simp
  have himage : ((fun u : Site => u + frame.child.modifiedDeck.combine (I u) (J u)) '' pairClass frame F p q).Finite :=
    frame.closedPolygon_finite.subset (by
      rintro _ ⟨u, -, rfl⟩
      exact hIJ u)
  exact Set.Finite.of_finite_image himage hinjOn

end PairClasses


section Gate

variable {frame : ChildFrame} {F : Field}

/-- The count of the same-pair sites with a smaller rank: the natural bulk order of `S3NoFortInputs`. -/
noncomputable def bulkCount (frame : ChildFrame) (F : Field) (R : Site → ℤ) (z : Site) : ℕ :=
  Set.ncard {u | u ∈ pairClass frame F (frame.cutGrade F 1 0 1 z) (frame.cutGrade F 0 1 1 z) ∧ R u < R z}

theorem bulkCount_lt {cU cV : ℤ} (hper : HasGeneratorPeriods frame.child F cU cV) (R : Site → ℤ) {c i : Site}
    (hP : frame.cutGrade F 1 0 1 i = frame.cutGrade F 1 0 1 c)
    (hJ : frame.cutGrade F 0 1 1 i = frame.cutGrade F 0 1 1 c) (hR : R i < R c) :
    bulkCount frame F R i < bulkCount frame F R c := by
  unfold bulkCount
  rw [hP, hJ]
  apply Set.ncard_lt_ncard
  · refine ⟨fun u hu => ⟨hu.1, lt_trans hu.2 hR⟩, fun h => ?_⟩
    have hi := h ⟨⟨hP, hJ⟩, hR⟩
    exact lt_irrefl _ hi.2
  · exact (pairClass_finite hper _ _).subset (fun u hu => hu.1)

/-- The unit sign: `1 • σ = σ` in the permit of the S3 game. -/
theorem one_shift_fun (frame : ChildFrame) (F : Field) :
    (fun z => F (z + (1 : ℤ) • frame.shortShift)) = (fun z => F (z + frame.shortShift)) := by
  funext z
  rw [one_smul]

/-- The permitted inputs of the unit game are the S3 permits of the plus sign. -/
theorem permitted_one {frame : ChildFrame} {F : Field} (C : CanonicalPolicy frame F 1) (c i : Site) (h : C.policy c i) :
    slipPermits F (fun z => F (z + frame.shortShift)) c i := by
  have := C.permitted c i h
  rw [one_shift_fun] at this
  exact this

/-- A restricted fort has, at each of its sites, a selected input in the fort. -/
theorem exists_input_in_fort {η : ℤ} (C : CanonicalPolicy frame F η) {fort : Set Site}
    (hfort : IsRestrictedFort F (slipPermits F (fun z => F (z + η • frame.shortShift))) fort) {z : Site} (hz : z ∈ fort) :
    ∃ i, (i = incomingNeg z ∨ i = incomingPos z) ∧ C.policy z i ∧ i ∈ fort := by
  rcases hfort z hz with ⟨hB, hcase⟩ | ⟨hW, hcaseN, hcaseP⟩
  · obtain ⟨hpn, hpp⟩ := C.quota.1 z hB
    have hn := C.permitted z _ hpn
    have hp := C.permitted z _ hpp
    rcases hcase with h | h
    · exact ⟨incomingNeg z, Or.inl rfl, hpn, h.resolve_right (fun h' => h' hn)⟩
    · exact ⟨incomingPos z, Or.inr rfl, hpp, h.resolve_right (fun h' => h' hp)⟩
  · rcases C.quota.2 z hW with hpn | hpp
    · have hn := C.permitted z _ hpn
      exact ⟨incomingNeg z, Or.inl rfl, hpn, hcaseN.resolve_right (fun h' => h' hn)⟩
    · have hp := C.permitted z _ hpp
      exact ⟨incomingPos z, Or.inr rfl, hpp, hcaseP.resolve_right (fun h' => h' hp)⟩

/-- The chain of the gate: from a fort site at the level `(c0, j0)`, follow selected inputs in the fort; a strict componentwise
drop ends the chain, a constant pair strictly lowers the count, and a free site ends the chain. -/
theorem gate_chain {η : ℤ} (C : CanonicalPolicy frame F η) {cU cV : ℤ} (hper : HasGeneratorPeriods frame.child F cU cV)
    {fort : Set Site} (hfort : IsRestrictedFort F (slipPermits F (fun z => F (z + η • frame.shortShift))) fort)
    (c0 j0 : ℤ) : ∀ n : ℕ, ∀ z : Site, bulkCount frame F C.rank z = n → z ∈ fort →
      frame.cutGrade F 1 0 1 z = c0 → frame.cutGrade F 0 1 1 z = j0 →
      (∃ t ∈ fort, frame.cutGrade F 1 0 1 t ≤ c0 ∧ frame.cutGrade F 0 1 1 t ≤ j0 ∧
          (frame.cutGrade F 1 0 1 t < c0 ∨ frame.cutGrade F 0 1 1 t < j0)) ∨
        (∃ t ∈ fort, C.free t ∧ frame.cutGrade F 1 0 1 t = c0 ∧ frame.cutGrade F 0 1 1 t = j0 ∧
          bulkCount frame F C.rank t ≤ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hz hP hJ
    by_cases hfree : C.free z
    · exact Or.inr ⟨z, hz, hfree, hP, hJ, hn.le⟩
    · obtain ⟨i, -, hpol, hifort⟩ := exists_input_in_fort C hfort hz
      have hmP := C.nonincreasingP z i hpol
      have hmJ := C.nonincreasingJ z i hpol
      by_cases hpair : frame.cutGrade F 1 0 1 i = c0 ∧ frame.cutGrade F 0 1 1 i = j0
      · have hlt : bulkCount frame F C.rank i < n := by
          rw [← hn]
          exact bulkCount_lt hper C.rank (by rw [hpair.1, hP]) (by rw [hpair.2, hJ])
            (C.strictRank z i hpol (by rw [hpair.1, hP]) (by rw [hpair.2, hJ]))
        rcases ih _ hlt i rfl hifort hpair.1 hpair.2 with h | ⟨t, ht, htf, htP, htJ, htle⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, ht, htf, htP, htJ, le_trans htle hlt.le⟩
      · have hPi : frame.cutGrade F 1 0 1 i ≤ c0 := by
          rw [← hP]
          exact hmP
        have hJi : frame.cutGrade F 0 1 1 i ≤ j0 := by
          rw [← hJ]
          exact hmJ
        refine Or.inl ⟨i, hifort, hPi, hJi, ?_⟩
        by_contra hcon
        rw [not_or, not_lt, not_lt] at hcon
        exact hpair ⟨le_antisymm hPi hcon.1, le_antisymm hJi hcon.2⟩

/-- The gate of `S3NoFortInputs` at a free site of a fort at the levels `(c0, j0)`: the start has a selected input in the fort,
and either it is a strict drop or the chain reaches a free site of strictly smaller count. -/
theorem gate_from_free {η : ℤ} (C : CanonicalPolicy frame F η) {cU cV : ℤ} (hper : HasGeneratorPeriods frame.child F cU cV)
    {fort : Set Site} (hfort : IsRestrictedFort F (slipPermits F (fun z => F (z + η • frame.shortShift))) fort)
    {site : Site} (hsite : site ∈ fort) (c0 j0 : ℤ)
    (hP : frame.cutGrade F 1 0 1 site = c0) (hJ : frame.cutGrade F 0 1 1 site = j0) :
    ∃ target ∈ fort, (frame.cutGrade F 1 0 1 target ≤ c0 ∧ frame.cutGrade F 0 1 1 target ≤ j0 ∧
        (frame.cutGrade F 1 0 1 target < c0 ∨ frame.cutGrade F 0 1 1 target < j0)) ∨
      (C.free target ∧ frame.cutGrade F 1 0 1 target = c0 ∧ frame.cutGrade F 0 1 1 target = j0 ∧
        bulkCount frame F C.rank target < bulkCount frame F C.rank site) := by
  obtain ⟨i, -, hpol, hifort⟩ := exists_input_in_fort C hfort hsite
  have hmP := C.nonincreasingP site i hpol
  have hmJ := C.nonincreasingJ site i hpol
  by_cases hpair : frame.cutGrade F 1 0 1 i = c0 ∧ frame.cutGrade F 0 1 1 i = j0
  · have hlt : bulkCount frame F C.rank i < bulkCount frame F C.rank site :=
      bulkCount_lt hper C.rank (by rw [hpair.1, hP]) (by rw [hpair.2, hJ])
        (C.strictRank site i hpol (by rw [hpair.1, hP]) (by rw [hpair.2, hJ]))
    rcases gate_chain C hper hfort c0 j0 _ i rfl hifort hpair.1 hpair.2 with
      ⟨t, ht, hA⟩ | ⟨t, ht, htf, htP, htJ, htle⟩
    · exact ⟨t, ht, Or.inl hA⟩
    · exact ⟨t, ht, Or.inr ⟨htf, htP, htJ, lt_of_le_of_lt htle hlt⟩⟩
  · have hPi : frame.cutGrade F 1 0 1 i ≤ c0 := by
      rw [← hP]
      exact hmP
    have hJi : frame.cutGrade F 0 1 1 i ≤ j0 := by
      rw [← hJ]
      exact hmJ
    refine ⟨i, hifort, Or.inl ⟨hPi, hJi, ?_⟩⟩
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact hpair ⟨le_antisymm hPi hcon.1, le_antisymm hJi hcon.2⟩

/-- **The S3 orders and the gate from the canonical signed policy.** The natural orders are the same-pair counts; the free set is
the policy's; the levels are `(c_0, 0)` with `c_0 = cutPrice`. -/
noncomputable def S3NoFortInputs_of_canonical (C : CanonicalPolicy frame F 1) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) : S3NoFortInputs frame F where
  free := C.free
  bulkOrder := bulkCount frame F C.rank
  freeOrder := bulkCount frame F C.rank
  firstLevel := frame.cutPrice
  secondLevel := 0
  freeInvariant := C.freeInvariant
  bulkBlack := by
    intro c _ hlap i hi _
    have hpol : C.policy c i := by
      rcases hi with rfl | rfl
      · exact (C.quota.1 c hlap).1
      · exact (C.quota.1 c hlap).2
    exact ⟨C.nonincreasingP c i hpol, C.nonincreasingJ c i hpol,
      fun hP hJ => bulkCount_lt hper C.rank hP hJ (C.strictRank c i hpol hP hJ)⟩
  bulkWhite := by
    intro c _ hlap
    rcases C.quota.2 c hlap with hpn | hpp
    · exact ⟨incomingNeg c, Or.inl rfl, permitted_one C c _ hpn, C.nonincreasingP c _ hpn, C.nonincreasingJ c _ hpn,
        fun hP hJ => bulkCount_lt hper C.rank hP hJ (C.strictRank c _ hpn hP hJ)⟩
    · exact ⟨incomingPos c, Or.inr rfl, permitted_one C c _ hpp, C.nonincreasingP c _ hpp, C.nonincreasingJ c _ hpp,
        fun hP hJ => bulkCount_lt hper C.rank hP hJ (C.strictRank c _ hpp hP hJ)⟩
  gate := by
    intro fort hfort site hsite _ hP hJ
    have hfort' : IsRestrictedFort F (slipPermits F (fun z => F (z + (1 : ℤ) • frame.shortShift))) fort := by
      rw [one_shift_fun]
      exact hfort
    exact gate_from_free C hper hfort' hsite _ _ hP hJ

end Gate

/-- Permitted black and white centres: the canonical policy is local in the sense of `PermitLocal`. -/
theorem permitLocal_of_canonical {η : ℤ} (C : CanonicalPolicy frame F η) :
    PermitLocal F (slipPermits F (fun z => F (z + η • frame.shortShift))) := by
  refine ⟨fun c hc => ⟨C.permitted c _ (C.quota.1 c hc).1, C.permitted c _ (C.quota.1 c hc).2⟩, fun c hc => ?_⟩
  rcases C.quota.2 c hc with h | h
  · exact Or.inl (C.permitted c _ h)
  · exact Or.inr (C.permitted c _ h)

/-- **The restricted no-fort premise of S3 from the canonical signed policy** (the S3 orders and gate of fix Q1). -/
theorem restrictedNoFort_of_canonical (C : CanonicalPolicy frame F 1) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hbinary : ∀ site, laplacian F site = -1 ∨ laplacian F site = 0) :
    RestrictedNoFort F (frame.cutGrade F 1 1 1) (slipPermits F (fun z => F (z + frame.shortShift))) :=
  restrictedNoFort_S3_of_inputs frame hper hbinary (by
    have := permitLocal_of_canonical C
    rw [one_shift_fun] at this
    exact this) (S3NoFortInputs_of_canonical C hper)

end FLatticePaper.Induction
