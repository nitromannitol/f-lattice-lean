import FLatticePaper.Tiles.AltLatticeOddW

/-! # Item (b) of `lemma:weak_alternate_odometer_properties` at the corrected odd child (after a `2`): the self-overlap

At a word `u 2` the parents are `p₁ = p_u + q_u` and `q₁ = q_u`, and the odd alternate tile is the six standard copies, without
an alternate parent piece. The bounds `L_r` of `AltItem4OddH.sepr` still separate `T(p₁)^{-,2} + W` and `T(q₁)^- + W` from the
tile: the margins are positive once `p₁ - q₁ = p_u` lies in the unit interval (`type_two_full`). Every `y` with `y, y + W` in the
tile then lies in `T(p₁)^{+,1}`, or in `(Q^+, P^{-,1} + W)`, or in `(P^{+,2}, Q^- + W)` (`classify_W2`). -/

namespace FLatticePaper.Tiles.AltLatticeCorrO

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.AltItem4 (latV latV1 fracOf hOdd Lr_pcopy Lr_qcopy)
open FLatticePaper.Tiles.AltLatticeOddW (sep_pp mid_P sep_qq mid_data)
open FLatticePaper.Tiles.SiteInduction (InH)

/-- At `u 2`: `0 ≤ n_{p₁} - n_{q₁} < d_{p₁} - d_{q₁}` (the difference is the odd parent of `u`). -/
theorem type_two_full (u : Word) :
    0 ≤ (parentsAt (u ++ [Digit.two])).odd.num - (parentsAt (u ++ [Digit.two])).even.num ∧
      (parentsAt (u ++ [Digit.two])).odd.num - (parentsAt (u ++ [Digit.two])).even.num + 1 ≤
        (parentsAt (u ++ [Digit.two])).odd.den - (parentsAt (u ++ [Digit.two])).even.den := by
  have hv := parentsAt_valid u
  have h1 := hv.odd_bounds
  have h3 := hv.odd_parity
  unfold Fraction.InUnitInterval at h1
  unfold Fraction.Odd at h3
  rw [(HorizontalStep.par_two u).1, (HorizontalStep.par_two u).2]
  simp only [Parents.current, Parents.combine]
  omega

theorem marg2_true_M2 (n1 d1 n2 d2 : ℤ) (h3 : 0 < n2) (h4 : n2 < d2) (hc : 0 ≤ n1 - n2) (he : n1 - n2 + 1 ≤ d1 - d2) :
    0 < d1 * d2 + 3 * d1 * n2 - 3 * d1 + d2 ^ 2 - d2 * n1 + 2 * d2 * n2 - 3 * d2 - n1 * n2 + n1 - n2 ^ 2 + n2 := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 1 + (f : ℤ) := ⟨(n2 - 1).toNat, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 1 + (f : ℤ) + 1 + (g : ℤ) := ⟨(d2 - 2 - f).toNat, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (f : ℤ) + (a : ℤ) := ⟨(n1 - 1 - f).toNat, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (f : ℤ) + 1 + (g : ℤ) + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 3 - f - g - a).toNat, by omega⟩
  ring_nf; positivity

theorem marg2_true_Qm (n1 d1 n2 d2 : ℤ) (h3 : 0 < n2) (h4 : n2 < d2) (hc : 0 ≤ n1 - n2) (he : n1 - n2 + 1 ≤ d1 - d2) :
    0 < d1 ^ 2 + d1 * d2 + 2 * d1 * n1 + 2 * d1 * n2 - 3 * d1 - 3 * d2 - n1 ^ 2 - n1 * n2 + n1 + n2 := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 1 + (f : ℤ) := ⟨(n2 - 1).toNat, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 1 + (f : ℤ) + 1 + (g : ℤ) := ⟨(d2 - 2 - f).toNat, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (f : ℤ) + (a : ℤ) := ⟨(n1 - 1 - f).toNat, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (f : ℤ) + 1 + (g : ℤ) + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 3 - f - g - a).toNat, by omega⟩
  ring_nf; positivity

theorem marg2_false_M2 (n1 d1 n2 d2 : ℤ) (h3 : 0 < n2) (h4 : n2 < d2) (hc : 0 ≤ n1 - n2) (he : n1 - n2 + 1 ≤ d1 - d2) :
    0 < d1 * d2 + 2 * d1 * n2 - 3 * d1 + d2 ^ 2 + 2 * d2 * n2 - 3 * d2 - n1 * n2 + n1 - n2 ^ 2 + n2 := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 1 + (f : ℤ) := ⟨(n2 - 1).toNat, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 1 + (f : ℤ) + 1 + (g : ℤ) := ⟨(d2 - 2 - f).toNat, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (f : ℤ) + (a : ℤ) := ⟨(n1 - 1 - f).toNat, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (f : ℤ) + 1 + (g : ℤ) + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 3 - f - g - a).toNat, by omega⟩
  ring_nf; positivity

theorem marg2_false_Qm (n1 d1 n2 d2 : ℤ) (h3 : 0 < n2) (h4 : n2 < d2) (hc : 0 ≤ n1 - n2) (he : n1 - n2 + 1 ≤ d1 - d2) :
    0 < d1 ^ 2 + d1 * d2 + 2 * d1 * n1 - 3 * d1 + 2 * d2 * n1 - 3 * d2 - n1 ^ 2 - n1 * n2 + n1 + n2 := by
  obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 1 + (f : ℤ) := ⟨(n2 - 1).toNat, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 1 + (f : ℤ) + 1 + (g : ℤ) := ⟨(d2 - 2 - f).toNat, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (f : ℤ) + (a : ℤ) := ⟨(n1 - 1 - f).toNat, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (f : ℤ) + 1 + (g : ℤ) + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 3 - f - g - a).toNat, by omega⟩
  ring_nf; positivity

/-- `L_r` separates `T(p₁)^{-,2} + W` and `T(q₁)^- + W` from `T̂(p₀)` at `u 2`. -/
theorem sepr2 (u : Word) (hw : ¬ IsBase (u ++ [Digit.two])) (T : Tile) (a z : Site)
    (ha : (T = (stateAt (u ++ [Digit.two])).tOdd ∧
        a = AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) ∨
      (T = (stateAt (u ++ [Digit.two])).tEven ∧ a = AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus))
    (h1 : z ∈ altOddTile AltRotStep.B (u ++ [Digit.two])) (h2 : z - latV (u ++ [Digit.two]) false 0 1 ∈ shift T a) : False := by
  have hD := (altOdd_halfTurn (u ++ [Digit.two]) z).1 h1
  have hU := ((AltBounds.claim_all (u ++ [Digit.two])).1 _ hD).1
  obtain ⟨hc, he⟩ := type_two_full u
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := parents_facts hw
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hL := Lr_pcopy hw _ _ h2
    rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
      rw [hph] at hdet <;> norm_num at hdet <;>
      simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, centreOdd, latV, latV1, fracOf, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true] at hU hL <;>
      generalize (parentsAt (u ++ [Digit.two])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [Digit.two])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [Digit.two])).even.num = n2 at * <;> generalize (parentsAt (u ++ [Digit.two])).even.den = d2 at *
    · nlinarith [marg2_true_M2 n1 d1 n2 d2 h3 h4 hc he]
    · nlinarith [marg2_false_M2 n1 d1 n2 d2 h3 h4 hc he]
  · have hL := Lr_qcopy hw _ _ h2
    rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] at hU hL <;>
      rw [hph] at hdet <;> norm_num at hdet <;>
      simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, centreOdd, latV, latV1, fracOf, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true] at hU hL <;>
      generalize (parentsAt (u ++ [Digit.two])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [Digit.two])).odd.den = d1 at * <;>
    generalize (parentsAt (u ++ [Digit.two])).even.num = n2 at * <;> generalize (parentsAt (u ++ [Digit.two])).even.den = d2 at *
    · nlinarith [marg2_true_Qm n1 d1 n2 d2 h3 h4 hc he]
    · nlinarith [marg2_false_Qm n1 d1 n2 d2 h3 h4 hc he]

/-- **The self-overlap along `W` at `u 2`.** -/
theorem classify_W2 (u : Word) (hw : ¬ IsBase (u ++ [Digit.two])) (y : Site)
    (hy : y ∈ altOddTile AltRotStep.B (u ++ [Digit.two])) (hyW : y + latV (u ++ [Digit.two]) false 0 1 ∈ altOddTile AltRotStep.B (u ++ [Digit.two])) :
    y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) ∨ (y ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) ∧ y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus)) ∨
      (y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) ∧ y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus)) := by
  have hzW : y + latV (u ++ [Digit.two]) false 0 1 - latV (u ++ [Digit.two]) false 0 1 = y := add_sub_cancel_right _ _
  -- the pieces that cannot carry `y` or `y + W`
  have hK3 : y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) → False := fun h =>
    sepr2 u hw _ _ (y + latV (u ++ [Digit.two]) false 0 1) (Or.inl ⟨rfl, rfl⟩) hyW (by rw [hzW]; exact h)
  have hK5 : y ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus) → False := fun h =>
    sepr2 u hw _ _ (y + latV (u ++ [Digit.two]) false 0 1) (Or.inr ⟨rfl, rfl⟩) hyW (by rw [hzW]; exact h)
  have hD : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - y ∈ altOddTile AltRotStep.B (u ++ [Digit.two]) := (altOdd_halfTurn (u ++ [Digit.two]) y).1 hy
  have hJ0 : y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) → False := fun h => by
    have h' := AltItem4.pcopy_refl hw (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even) _ _ h
    rw [AltItem4.refl_P1 hw] at h'
    exact sepr2 u hw _ _ (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - y) (Or.inl ⟨rfl, rfl⟩) hD (by convert h' using 1; abel)
  have hJ4 : y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) → False := fun h => by
    have h' := AltItem4.qcopy_refl hw (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even) _ _ h
    rw [AltItem4.refl_Qp hw] at h'
    exact sepr2 u hw _ _ (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - y) (Or.inr ⟨rfl, rfl⟩) hD (by convert h' using 1; abel)
  have hJ3 : y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) → y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) := fun h => by
    rw [← AltItem4.overlap_id, AltItem4.mem_shift_shift_iff] at h
    simpa using h
  -- the decompositions
  obtain ⟨y', hy', he⟩ := altOddTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have hy1 := hy
  have hy2 := hyW
  rw [he, AltItem4.altQ1Part_two, Finset.union_empty] at hy1 hy2
  rw [mem_oddStd_iff] at hy1 hy2
  rcases hy1 with ⟨a, ha, hK⟩ | ⟨a, ha, hK⟩ <;> rcases hy2 with ⟨b, hb, hJ⟩ | ⟨b, hb, hJ⟩ <;>
    simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  · -- `y` and `y + W` in copies of `T(p₁)`
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl hK
    · rcases hb with rfl | rfl | rfl | rfl
      · exact (hJ0 hJ).elim
      · exact (sep_pp hw _ y hK hJ).elim
      · exact Or.inl (hJ3 (mid_P hw _ _ _ (mid_data _ hw).1 (mid_data _ hw).2.2.1 y hJ hK))
      · exact Or.inl (hJ3 hJ)
    · rcases hb with rfl | rfl | rfl | rfl
      · exact (hJ0 hJ).elim
      · exact Or.inl (hJ3 (mid_P hw _ _ _ (mid_data _ hw).2.1 (mid_data _ hw).2.2.2 y hJ hK))
      · exact (sep_pp hw _ y hK hJ).elim
      · exact Or.inl (hJ3 hJ)
    · exact (hK3 hK).elim
  · -- `y` in a copy of `T(p₁)`, `y + W` in a copy of `T(q₁)`
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl hK
    · rcases hb with rfl | rfl
      · exact (hJ4 hJ).elim
      · exact Or.inr (Or.inr ⟨hK, hJ⟩)
    · rcases hb with rfl | rfl
      · exact (hJ4 hJ).elim
      · rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hK hJ
        · exact (AltItem4.sep_odd_true_01_52 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
        · exact (AltItem4.sep_odd_false_01_52 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
    · exact (hK3 hK).elim
  · -- `y` in a copy of `T(q₁)`, `y + W` in a copy of `T(p₁)`
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl | rfl | rfl
      · exact (hJ0 hJ).elim
      · rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hK hJ
        · exact (AltItem4.sep_odd_true_01_14 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
        · exact (AltItem4.sep_odd_false_01_14 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
      · exact Or.inr (Or.inl ⟨hK, hJ⟩)
      · exact Or.inl (hJ3 hJ)
    · exact (hK5 hK).elim
  · -- both in copies of `T(q₁)`
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · exact (hJ4 hJ).elim
      · exact (sep_qq hw y hJ hK).elim
    · exact (hK5 hK).elim

end FLatticePaper.Tiles.AltLatticeCorrO
