import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StandardField

/-! The star estimates S1 and S2 of the sewn standard field, reduced to the star of the fundamental polygon `E`
(task 18). The difference `D = F − F(· + σ)` with `σ = shortShift` is periodic under the kernel and shifts by `2`
under the transverse vector, so the unit-slip and no-saddle conditions are invariant under the deck. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- The difference `D = F − F(· + σ)` of a field and its translate by `σ`. -/
def starDiff (F : Field) (σ : Site) : Field := fun z => F z - F (z + σ)

section Shift

variable {F : Field} {K V σ : Site} {cU cV : ℤ} {g : Site → ℤ}

theorem starDiff_add_kernel (hK : ∀ z, F (z + K) = F z + cU) (z : Site) :
    starDiff F σ (z + K) = starDiff F σ z := by
  unfold starDiff
  rw [add_right_comm z K σ, hK z, hK (z + σ)]
  ring

theorem starDiff_add_transverse (hV : ∀ z, F (z + V) = F z - g z + cV)
    (hgσ : ∀ z, g (z + σ) = g z + g σ) (z : Site) :
    starDiff F σ (z + V) = starDiff F σ z + g σ := by
  unfold starDiff
  rw [add_right_comm z V σ, hV z, hV (z + σ), hgσ z]
  ring

theorem starDiff_add_zsmul_kernel (hK : ∀ z, F (z + K) = F z + cU) (i : ℤ) :
    ∀ z : Site, starDiff F σ (z + i • K) = starDiff F σ z := by
  refine Int.induction_on i ?_ ?_ ?_
  · intro z; simp
  · intro n ih z
    have e : z + ((n : ℤ) + 1) • K = (z + (n : ℤ) • K) + K := by
      simp only [add_smul, one_smul]; abel
    rw [e, starDiff_add_kernel hK, ih z]
  · intro n ih z
    have e : z + (-(n : ℤ) - 1) • K + K = z + (-(n : ℤ)) • K := by
      simp only [sub_smul, one_smul]; abel
    have h1 := starDiff_add_kernel (σ := σ) hK (z + (-(n : ℤ) - 1) • K)
    rw [e, ih z] at h1
    exact h1.symm

theorem starDiff_add_zsmul_transverse (hV : ∀ z, F (z + V) = F z - g z + cV)
    (hgσ : ∀ z, g (z + σ) = g z + g σ) (j : ℤ) :
    ∀ z : Site, starDiff F σ (z + j • V) = starDiff F σ z + j * g σ := by
  refine Int.induction_on j ?_ ?_ ?_
  · intro z; simp
  · intro n ih z
    have e : z + ((n : ℤ) + 1) • V = (z + (n : ℤ) • V) + V := by
      simp only [add_smul, one_smul]; abel
    rw [e, starDiff_add_transverse hV hgσ, ih z]
    ring
  · intro n ih z
    have e : z + (-(n : ℤ) - 1) • V + V = z + (-(n : ℤ)) • V := by
      simp only [sub_smul, one_smul]; abel
    have h1 := starDiff_add_transverse (σ := σ) hV hgσ (z + (-(n : ℤ) - 1) • V)
    rw [e, ih z] at h1
    linarith

end Shift

/-- A deck vector with even coordinate sum: integer combinations of two even vectors are even. -/
theorem evenSite_smul_add (K V : Site) (hK : EvenSite K) (hV : EvenSite V) (i j : ℤ) :
    EvenSite (i • K + j • V) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, K.1 + K.2 = 2 * a := ⟨(K.1 + K.2) / 2, by unfold EvenSite at hK; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, V.1 + V.2 = 2 * b := ⟨(V.1 + V.2) / 2, by unfold EvenSite at hV; omega⟩
  refine evenSite_of_sum _ (i * a + j * b) ?_
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination i * ha + j * hb

theorem combine_eq_smul (deck : PeriodDeck) (i j : ℤ) :
    deck.combine i j = i • deck.kernel + j • deck.transverse := by
  ext <;> simp [PeriodDeck.combine, zsmul_eq_mul]

/-- Translation by an even vector preserves the edge relation. -/
theorem edge_add_even {u z g : Site} (hg : EvenSite g) : Edge (u + g) (z + g) ↔ Edge u z := by
  unfold Edge
  rw [incomingNeg_add_of_even z g hg, incomingPos_add_of_even z g hg]
  constructor
  · rintro (h | h)
    · exact Or.inl (add_right_cancel h)
    · exact Or.inr (add_right_cancel h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem slip_eq_starDiff (F : Field) (σ z u : Site) :
    slipIncrement F (fun w => F (w + σ)) z u = starDiff F σ u - starDiff F σ z := rfl

/-- The star estimates S1 and S2 of a field with generator periods, from the star conditions on `E`. The deck
vectors `i K + j V` are even and `starDiff` shifts by `2 j` along them, so checking the centres of `E` suffices. -/
theorem star_of_deck {F : Field} {K V σ : Site} {cU cV : ℤ} {g : Site → ℤ} {E : Set Site}
    (hKe : EvenSite K) (hVe : EvenSite V)
    (hK : ∀ z, F (z + K) = F z + cU) (hV : ∀ z, F (z + V) = F z - g z + cV)
    (hgσ : ∀ z, g (z + σ) = g z + g σ) (hgσ2 : g σ = 2)
    (hcover : ∀ z, ∃ y ∈ E, ∃ i j : ℤ, z = y + (i • K + j • V))
    (hEr : ∀ e ∈ E, starDiff F σ e = 0 ∨ starDiff F σ e = 1 ∨ starDiff F σ e = 2)
    (hNr : ∀ e ∈ E, ∀ u, Edge u e → (starDiff F σ u = 0 ∨ starDiff F σ u = 1 ∨ starDiff F σ u = 2))
    (hJ : ∀ e ∈ E, ∀ u, Edge u e →
      ¬((starDiff F σ e = 0 ∧ starDiff F σ u = 2) ∨ (starDiff F σ e = 2 ∧ starDiff F σ u = 0))) :
    HasUnitSlip F (fun z => F (z + σ)) ∧ NoEvenSlipSaddle F (fun z => F (z + σ)) := by
  have hdeck : ∀ i j : ℤ, EvenSite (i • K + j • V) := fun i j => evenSite_smul_add K V hKe hVe i j
  have shift : ∀ (z : Site) (i j : ℤ),
      starDiff F σ (z + (i • K + j • V)) = starDiff F σ z + 2 * j := by
    intro z i j
    rw [show z + (i • K + j • V) = (z + i • K) + j • V by abel,
      starDiff_add_zsmul_transverse hV hgσ j (z + i • K), starDiff_add_zsmul_kernel hK i z, hgσ2]
    ring
  constructor
  · intro center input hedge
    obtain ⟨e, he, i, j, rfl⟩ := hcover center
    have hk : Edge (input - (i • K + j • V)) e :=
      (edge_add_even (u := input - (i • K + j • V)) (z := e) (hdeck i j)).mp
        (by rw [sub_add_cancel]; exact hedge)
    have h1 := shift (input - (i • K + j • V)) i j
    rw [sub_add_cancel] at h1
    have h2 := shift e i j
    have hA := hEr e he
    have hB := hNr e he (input - (i • K + j • V)) hk
    have hC := hJ e he (input - (i • K + j • V)) hk
    rw [slip_eq_starDiff, h1, h2]
    constructor <;> omega
  · intro site hsite
    obtain ⟨e, he, i, j, rfl⟩ := hcover site
    have hsite' : starDiff F σ (e + (i • K + j • V)) % 2 = 0 := hsite
    have h2 := shift e i j
    have hEven : starDiff F σ e % 2 = 0 := by omega
    have hA := hEr e he
    have hNeg := hNr e he (incomingNeg e) (Or.inl rfl)
    have hPos := hNr e he (incomingPos e) (Or.inr rfl)
    have hin_neg : incomingNeg (e + (i • K + j • V)) = incomingNeg e + (i • K + j • V) :=
      incomingNeg_add_of_even e _ (hdeck i j)
    have hin_pos : incomingPos (e + (i • K + j • V)) = incomingPos e + (i • K + j • V) :=
      incomingPos_add_of_even e _ (hdeck i j)
    dsimp only
    rw [slip_eq_starDiff, slip_eq_starDiff, hin_neg, hin_pos, shift (incomingNeg e) i j,
      shift (incomingPos e) i j, h2]
    omega

/-- The star estimates of the sewn standard field, for a child frame: the deck is the child's, and the star
conditions are on the closed polygon `E` and its incoming sites. -/
theorem ChildFrame.star_of_closedPolygon (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hEr : ∀ e ∈ frame.closedPolygon, starDiff F frame.shortShift e = 0 ∨ starDiff F frame.shortShift e = 1 ∨
      starDiff F frame.shortShift e = 2)
    (hNr : ∀ e ∈ frame.closedPolygon, ∀ u, Edge u e →
      (starDiff F frame.shortShift u = 0 ∨ starDiff F frame.shortShift u = 1 ∨
        starDiff F frame.shortShift u = 2))
    (hJ : ∀ e ∈ frame.closedPolygon, ∀ u, Edge u e →
      ¬((starDiff F frame.shortShift e = 0 ∧ starDiff F frame.shortShift u = 2) ∨
        (starDiff F frame.shortShift e = 2 ∧ starDiff F frame.shortShift u = 0))) :
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
      NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) := by
  have hKspan : frame.child.modifiedDeck.kernel ∈ frame.child.modifiedDeck.span :=
    ⟨1, 0, by simp [PeriodDeck.combine]⟩
  have hVspan : frame.child.modifiedDeck.transverse ∈ frame.child.modifiedDeck.span :=
    ⟨0, 1, by simp [PeriodDeck.combine]⟩
  have hKe : EvenSite frame.child.modifiedDeck.kernel :=
    ((frame.child.mem_modifiedDeck_iff _).mp hKspan).2
  have hVe : EvenSite frame.child.modifiedDeck.transverse :=
    ((frame.child.mem_modifiedDeck_iff _).mp hVspan).2
  have hcover : ∀ z, ∃ y ∈ frame.closedPolygon, ∃ i j : ℤ,
      z = y + (i • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) := by
    intro z
    obtain ⟨y, hy, i, j, hz⟩ := frame.closedPolygon_covers z
    exact ⟨y, hy, i, j, by rw [hz, combine_eq_smul]⟩
  have hgσ : ∀ z, frame.child.transverseGrade (z + frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade frame.shortShift := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hgσ2 : frame.child.transverseGrade frame.shortShift = 2 := by
    rw [frame.transverseGrade_child, frame.tGrade_shortShift]
    norm_num
  exact star_of_deck hKe hVe hper.1 hper.2 hgσ hgσ2 hcover hEr hNr hJ

end FLatticePaper.Induction
