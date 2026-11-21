import FLatticePaper.Plane.Induction.Coherence
import FLatticePaper.Plane.Induction.Seams

/-! The sewn standard is binary: its zero and harmonic strips and its central reflection give the Laplacian
values `-1` or `0` on the whole plane (supplement Part I, step 1). -/

namespace FLatticePaper.Induction
open Farey

/-! ### Parity of the child -/

theorem ChildFrame.child_odd (frame : ChildFrame) :
    frame.child.num % 2 = 1 ∧ frame.child.den % 2 = 1 := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rcases Int.emod_two_eq_zero_or_one frame.child.num with h | h
  · exfalso
    have hd : frame.child.den % 2 = 0 := by omega
    obtain ⟨p, hp⟩ : ∃ p, frame.child.num = 2 * p := ⟨frame.child.num / 2, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, frame.child.den = 2 * q := ⟨frame.child.den / 2, by omega⟩
    obtain ⟨u, v, huv⟩ := frame.child_reduced
    have h2 : (2 : ℤ) ∣ 1 := ⟨u * p + v * q, by rw [← huv, hp, hq]; ring⟩
    norm_num at h2
  · exact ⟨h, by omega⟩

theorem ChildFrame.T_even (frame : ChildFrame) : frame.child.periodDenominator % 2 = 0 := by
  obtain ⟨-, -, -, -, hTdef⟩ := frame.child_facts
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by have := frame.child_odd; omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by have := frame.child_odd; omega⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, frame.child.periodDenominator = 2 * τ :=
    ⟨2 * b ^ 2 + 4 * b + 4 * a * b - 2 * a ^ 2 + 1, by rw [hTdef, ha, hb]; ring⟩
  omega

theorem ChildFrame.tGrade_parity (frame : ChildFrame) (z : Site) :
    ∃ c : ℤ, frame.tGrade z = z.1 + z.2 + 2 * c := by
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by have := frame.child_odd; omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by have := frame.child_odd; omega⟩
  exact ⟨a * z.1 - b * z.2 - z.2, by unfold ChildFrame.tGrade; rw [ha, hb]; ring⟩

theorem ChildFrame.sGrade_parity (frame : ChildFrame) (z : Site) :
    ∃ c : ℤ, frame.sGrade z = 2 * c := by
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by have := frame.child_odd; omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by have := frame.child_odd; omega⟩
  exact ⟨(b + a + 1) * z.1 + (b - a) * z.2, by unfold ChildFrame.sGrade; rw [ha, hb]; ring⟩

/-! ### Arithmetic of the band lemma

The four input cases of a site of `E`. All the grades are integers; the parities of `n`, `d`, `T` and of `s`
(always even) and of `t` (the parity of the site) are hypotheses. -/

theorem band_key_even_neg {N D T t s : ℤ} (hN : N % 2 = 1) (hD : D % 2 = 1) (hN1 : 1 ≤ N)
    (hND : N + 2 ≤ D) (hD3 : 3 ≤ D) (hT : T % 2 = 0) (hs : s % 2 = 0) (ht : t % 2 = 0)
    (hzt : 2 - T ≤ t ∧ t ≤ D + N - 2) (hzs : 0 ≤ s ∧ s ≤ T + 2 * N)
    (hout : ¬(N - T ≤ t - N ∧ t - N ≤ D ∧ 2 - D + N ≤ s - (D + N) ∧ s - (D + N) ≤ T + D + N - 2)) :
    (2 ≤ t ∧ t ≤ D + N - 2) ∨ (0 ≤ s ∧ s ≤ 2 * N) ∨
      (2 ≤ D + N - T - t ∧ D + N - T - t ≤ D + N - 2) ∨ (0 ≤ T + 2 * N - s ∧ T + 2 * N - s ≤ 2 * N) := by
  omega

theorem band_key_even_pos {N D T t s : ℤ} (hN : N % 2 = 1) (hD : D % 2 = 1) (hN1 : 1 ≤ N)
    (hND : N + 2 ≤ D) (hD3 : 3 ≤ D) (hT : T % 2 = 0) (hs : s % 2 = 0) (ht : t % 2 = 0)
    (hzt : 2 - T ≤ t ∧ t ≤ D + N - 2) (hzs : 0 ≤ s ∧ s ≤ T + 2 * N)
    (hout : ¬(N - T ≤ t + N ∧ t + N ≤ D ∧ 2 - D + N ≤ s + (D + N) ∧ s + (D + N) ≤ T + D + N - 2)) :
    (2 ≤ t ∧ t ≤ D + N - 2) ∨ (0 ≤ s ∧ s ≤ 2 * N) ∨
      (2 ≤ D + N - T - t ∧ D + N - T - t ≤ D + N - 2) ∨ (0 ≤ T + 2 * N - s ∧ T + 2 * N - s ≤ 2 * N) := by
  omega

theorem band_key_odd_neg {N D T t s : ℤ} (hN : N % 2 = 1) (hD : D % 2 = 1) (hN1 : 1 ≤ N)
    (hD3 : 3 ≤ D) (hT : T % 2 = 0) (hs : s % 2 = 0) (ht : t % 2 = 1)
    (hzt : N - T ≤ t ∧ t ≤ D) (hzs : 2 - D + N ≤ s ∧ s ≤ T + D + N - 2)
    (hout : ¬(2 - T ≤ t + D ∧ t + D ≤ D + N - 2 ∧ 0 ≤ s - (D - N) ∧ s - (D - N) ≤ T + 2 * N)) :
    (N ≤ t ∧ t ≤ D) ∨ (2 - D + N ≤ s ∧ s ≤ D + N - 2) ∨
      (N ≤ D + N - T - t ∧ D + N - T - t ≤ D) ∨ (2 - D + N ≤ T + 2 * N - s ∧ T + 2 * N - s ≤ D + N - 2) := by
  omega

theorem band_key_odd_pos {N D T t s : ℤ} (hN : N % 2 = 1) (hD : D % 2 = 1) (hN1 : 1 ≤ N)
    (hD3 : 3 ≤ D) (hT : T % 2 = 0) (hs : s % 2 = 0) (ht : t % 2 = 1)
    (hzt : N - T ≤ t ∧ t ≤ D) (hzs : 2 - D + N ≤ s ∧ s ≤ T + D + N - 2)
    (hout : ¬(2 - T ≤ t - D ∧ t - D ≤ D + N - 2 ∧ 0 ≤ s + (D - N) ∧ s + (D - N) ≤ T + 2 * N)) :
    (N ≤ t ∧ t ≤ D) ∨ (2 - D + N ≤ s ∧ s ≤ D + N - 2) ∨
      (N ≤ D + N - T - t ∧ D + N - T - t ≤ D) ∨ (2 - D + N ≤ T + 2 * N - s ∧ T + 2 * N - s ≤ D + N - 2) := by
  omega

/-! ### The four cases of a site of `E` with an input outside `E` -/

/-- The zero and harmonic strips of a field. -/
def ChildFrame.HasStrips (frame : ChildFrame) (F : Field) : Prop :=
  (∀ z, 1 - frame.child.den ≤ frame.tGrade z → frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 →
      F z = 0) ∧
  (∀ z, 1 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 → F z = harmonicGrid z)

theorem ChildFrame.mem_bands_even_neg (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon)
    (he : EvenSite z) (hout : (z.1 - 1, z.2) ∉ frame.closedPolygon) :
    z ∈ frame.hBand ∨ z ∈ frame.vBand ∨ frame.centre - z ∈ frame.hBand ∨ frame.centre - z ∈ frame.vBand := by
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  obtain ⟨hNo, hDo⟩ := frame.child_odd
  have hT := frame.T_even
  obtain ⟨c, hc⟩ := frame.tGrade_parity z
  obtain ⟨c', hc'⟩ := frame.sGrade_parity z
  have hpz : (z.1 + z.2) % 2 = 0 := he
  obtain ⟨⟨hzt1, hzt2⟩, hzs⟩ : (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∧
      (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨-, a1, a2, a3, a4⟩ | ⟨hno, -⟩
    · exact ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
    · exact absurd he hno
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite
    dsimp only
    omega
  have hout' : ¬(frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z - frame.child.num ∧
      frame.tGrade z - frame.child.num ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z - (frame.child.den + frame.child.num) ∧
      frame.sGrade z - (frame.child.den + frame.child.num) ≤
        frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    intro hh
    apply hout
    rw [frame.mem_closedPolygon_iff]
    refine Or.inr ⟨hodd, ?_⟩
    rw [frame.tGrade_sub_x, frame.sGrade_sub_x]
    exact hh
  have key := band_key_even_neg hNo hDo (by omega) (by omega) hD3 hT (by omega) (by omega)
    ⟨hzt1, hzt2⟩ hzs hout'
  rcases key with h | h | h | h
  · exact Or.inl ((frame.mem_hBand_iff z).mpr ⟨hz, by rw [if_pos he]; exact h⟩)
  · exact Or.inr (Or.inl ((frame.mem_vBand_iff z).mpr ⟨hz, by rw [if_pos he]; exact h⟩))
  · exact Or.inr (Or.inr (Or.inl ((frame.mem_hBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_pos ((frame.evenSite_centre_sub z).mpr he), frame.tGrade_sub, frame.tGrade_centre]
      exact h⟩)))
  · exact Or.inr (Or.inr (Or.inr ((frame.mem_vBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_pos ((frame.evenSite_centre_sub z).mpr he), frame.sGrade_sub, frame.sGrade_centre]
      exact h⟩)))

theorem ChildFrame.mem_bands_even_pos (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon)
    (he : EvenSite z) (hout : (z.1 + 1, z.2) ∉ frame.closedPolygon) :
    z ∈ frame.hBand ∨ z ∈ frame.vBand ∨ frame.centre - z ∈ frame.hBand ∨ frame.centre - z ∈ frame.vBand := by
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  obtain ⟨hNo, hDo⟩ := frame.child_odd
  have hT := frame.T_even
  obtain ⟨c, hc⟩ := frame.tGrade_parity z
  obtain ⟨c', hc'⟩ := frame.sGrade_parity z
  have hpz : (z.1 + z.2) % 2 = 0 := he
  obtain ⟨⟨hzt1, hzt2⟩, hzs⟩ : (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∧
      (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨-, a1, a2, a3, a4⟩ | ⟨hno, -⟩
    · exact ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
    · exact absurd he hno
  have hodd : ¬ EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite
    dsimp only
    omega
  have hout' : ¬(frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z + frame.child.num ∧
      frame.tGrade z + frame.child.num ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z + (frame.child.den + frame.child.num) ∧
      frame.sGrade z + (frame.child.den + frame.child.num) ≤
        frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    intro hh
    apply hout
    rw [frame.mem_closedPolygon_iff]
    refine Or.inr ⟨hodd, ?_⟩
    rw [frame.tGrade_add_x, frame.sGrade_add_x]
    exact hh
  have key := band_key_even_pos hNo hDo (by omega) (by omega) hD3 hT (by omega) (by omega)
    ⟨hzt1, hzt2⟩ hzs hout'
  rcases key with h | h | h | h
  · exact Or.inl ((frame.mem_hBand_iff z).mpr ⟨hz, by rw [if_pos he]; exact h⟩)
  · exact Or.inr (Or.inl ((frame.mem_vBand_iff z).mpr ⟨hz, by rw [if_pos he]; exact h⟩))
  · exact Or.inr (Or.inr (Or.inl ((frame.mem_hBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_pos ((frame.evenSite_centre_sub z).mpr he), frame.tGrade_sub, frame.tGrade_centre]
      exact h⟩)))
  · exact Or.inr (Or.inr (Or.inr ((frame.mem_vBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_pos ((frame.evenSite_centre_sub z).mpr he), frame.sGrade_sub, frame.sGrade_centre]
      exact h⟩)))

theorem ChildFrame.mem_bands_odd_neg (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon)
    (he : ¬ EvenSite z) (hout : (z.1, z.2 - 1) ∉ frame.closedPolygon) :
    z ∈ frame.hBand ∨ z ∈ frame.vBand ∨ frame.centre - z ∈ frame.hBand ∨ frame.centre - z ∈ frame.vBand := by
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  obtain ⟨hNo, hDo⟩ := frame.child_odd
  have hT := frame.T_even
  obtain ⟨c, hc⟩ := frame.tGrade_parity z
  obtain ⟨c', hc'⟩ := frame.sGrade_parity z
  have hpz : ¬ (z.1 + z.2) % 2 = 0 := he
  obtain ⟨⟨hzt1, hzt2⟩, hzs⟩ : (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den) ∧
      (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨hE, -⟩ | ⟨-, a1, a2, a3, a4⟩
    · exact absurd hE he
    · exact ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
  have hev : EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite
    dsimp only
    omega
  have hout' : ¬(2 - frame.child.periodDenominator ≤ frame.tGrade z + frame.child.den ∧
      frame.tGrade z + frame.child.den ≤ frame.child.den + frame.child.num - 2 ∧
      0 ≤ frame.sGrade z - (frame.child.den - frame.child.num) ∧
      frame.sGrade z - (frame.child.den - frame.child.num) ≤
        frame.child.periodDenominator + 2 * frame.child.num) := by
    intro hh
    apply hout
    rw [frame.mem_closedPolygon_iff]
    refine Or.inl ⟨hev, ?_⟩
    rw [frame.tGrade_sub_y, frame.sGrade_sub_y]
    exact hh
  have key := band_key_odd_neg hNo hDo (by omega) hD3 hT (by omega) (by omega)
    ⟨hzt1, hzt2⟩ hzs hout'
  rcases key with h | h | h | h
  · exact Or.inl ((frame.mem_hBand_iff z).mpr ⟨hz, by rw [if_neg he]; exact h⟩)
  · exact Or.inr (Or.inl ((frame.mem_vBand_iff z).mpr ⟨hz, by rw [if_neg he]; exact h⟩))
  · exact Or.inr (Or.inr (Or.inl ((frame.mem_hBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_neg (fun hh => he ((frame.evenSite_centre_sub z).mp hh)), frame.tGrade_sub, frame.tGrade_centre]
      exact h⟩)))
  · exact Or.inr (Or.inr (Or.inr ((frame.mem_vBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_neg (fun hh => he ((frame.evenSite_centre_sub z).mp hh)), frame.sGrade_sub, frame.sGrade_centre]
      exact h⟩)))

theorem ChildFrame.mem_bands_odd_pos (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon)
    (he : ¬ EvenSite z) (hout : (z.1, z.2 + 1) ∉ frame.closedPolygon) :
    z ∈ frame.hBand ∨ z ∈ frame.vBand ∨ frame.centre - z ∈ frame.hBand ∨ frame.centre - z ∈ frame.vBand := by
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  obtain ⟨hNo, hDo⟩ := frame.child_odd
  have hT := frame.T_even
  obtain ⟨c, hc⟩ := frame.tGrade_parity z
  obtain ⟨c', hc'⟩ := frame.sGrade_parity z
  have hpz : ¬ (z.1 + z.2) % 2 = 0 := he
  obtain ⟨⟨hzt1, hzt2⟩, hzs⟩ : (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den) ∧
      (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨hE, -⟩ | ⟨-, a1, a2, a3, a4⟩
    · exact absurd hE he
    · exact ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
  have hev : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite
    dsimp only
    omega
  have hout' : ¬(2 - frame.child.periodDenominator ≤ frame.tGrade z - frame.child.den ∧
      frame.tGrade z - frame.child.den ≤ frame.child.den + frame.child.num - 2 ∧
      0 ≤ frame.sGrade z + (frame.child.den - frame.child.num) ∧
      frame.sGrade z + (frame.child.den - frame.child.num) ≤
        frame.child.periodDenominator + 2 * frame.child.num) := by
    intro hh
    apply hout
    rw [frame.mem_closedPolygon_iff]
    refine Or.inl ⟨hev, ?_⟩
    rw [frame.tGrade_add_y, frame.sGrade_add_y]
    exact hh
  have key := band_key_odd_pos hNo hDo (by omega) hD3 hT (by omega) (by omega)
    ⟨hzt1, hzt2⟩ hzs hout'
  rcases key with h | h | h | h
  · exact Or.inl ((frame.mem_hBand_iff z).mpr ⟨hz, by rw [if_neg he]; exact h⟩)
  · exact Or.inr (Or.inl ((frame.mem_vBand_iff z).mpr ⟨hz, by rw [if_neg he]; exact h⟩))
  · exact Or.inr (Or.inr (Or.inl ((frame.mem_hBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_neg (fun hh => he ((frame.evenSite_centre_sub z).mp hh)), frame.tGrade_sub, frame.tGrade_centre]
      exact h⟩)))
  · exact Or.inr (Or.inr (Or.inr ((frame.mem_vBand_iff (frame.centre - z)).mpr ⟨frame.centre_sub_mem hz, by
      rw [if_neg (fun hh => he ((frame.evenSite_centre_sub z).mp hh)), frame.sGrade_sub, frame.sGrade_centre]
      exact h⟩)))

/-- A site of `E` with an input outside `E` lies in one of the four bands. -/
theorem ChildFrame.mem_bands_of_input_not_mem (frame : ChildFrame) {z u : Site}
    (hz : z ∈ frame.closedPolygon) (hu : Edge u z) (hout : u ∉ frame.closedPolygon) :
    z ∈ frame.hBand ∨ z ∈ frame.vBand ∨ frame.centre - z ∈ frame.hBand ∨ frame.centre - z ∈ frame.vBand := by
  by_cases he : EvenSite z
  · rcases hu with hu | hu
    · unfold incomingNeg at hu
      rw [if_pos he] at hu
      subst hu
      exact frame.mem_bands_even_neg hz he hout
    · unfold incomingPos at hu
      rw [if_pos he] at hu
      subst hu
      exact frame.mem_bands_even_pos hz he hout
  · rcases hu with hu | hu
    · unfold incomingNeg at hu
      rw [if_neg he] at hu
      subst hu
      exact frame.mem_bands_odd_neg hz he hout
    · unfold incomingPos at hu
      rw [if_neg he] at hu
      subst hu
      exact frame.mem_bands_odd_pos hz he hout

/-! ### The central reflection and the bands -/

/-- The reflection `z ↦ R − z` preserves the Laplacian of a field with the reflection identity. -/
theorem ChildFrame.laplacian_centre_sub (frame : ChildFrame) {F : Field}
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (z : Site) :
    laplacian F (frame.centre - z) = laplacian F z := by
  have hsum : frame.tGrade (incomingPos z) + frame.tGrade (incomingNeg z) = 2 * frame.tGrade z := by
    by_cases he : EvenSite z
    · simp only [incomingPos, incomingNeg, if_pos he]
      rw [frame.tGrade_add_x, frame.tGrade_sub_x]
      ring
    · simp only [incomingPos, incomingNeg, if_neg he]
      rw [frame.tGrade_add_y, frame.tGrade_sub_y]
      ring
  have hn : incomingNeg (frame.centre - z) = frame.centre - incomingPos z := by
    by_cases he : EvenSite z
    · have hR : EvenSite (frame.centre - z) := (frame.evenSite_centre_sub z).mpr he
      simp only [incomingNeg, incomingPos, if_pos he, if_pos hR]
      exact Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub])
    · have hR : ¬ EvenSite (frame.centre - z) := fun h => he ((frame.evenSite_centre_sub z).mp h)
      simp only [incomingNeg, incomingPos, if_neg he, if_neg hR]
      exact Prod.ext (by simp only [Prod.fst_sub]) (by simp only [Prod.snd_sub]; ring)
  have hp : incomingPos (frame.centre - z) = frame.centre - incomingNeg z := by
    by_cases he : EvenSite z
    · have hR : EvenSite (frame.centre - z) := (frame.evenSite_centre_sub z).mpr he
      simp only [incomingNeg, incomingPos, if_pos he, if_pos hR]
      exact Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub])
    · have hR : ¬ EvenSite (frame.centre - z) := fun h => he ((frame.evenSite_centre_sub z).mp h)
      simp only [incomingNeg, incomingPos, if_neg he, if_neg hR]
      exact Prod.ext (by simp only [Prod.fst_sub]) (by simp only [Prod.snd_sub]; ring)
  unfold laplacian
  rw [hn, hp, hrefl (incomingPos z), hrefl (incomingNeg z), hrefl z]
  linarith

/-! ### The bands carry Laplacian zero -/

/-- At a site of the horizontal band the zero strip contains the site and both its inputs. -/
theorem ChildFrame.laplacian_eq_zero_of_hBand (frame : ChildFrame) {F : Field}
    (hstrips : frame.HasStrips F) {w : Site} (hw : w ∈ frame.hBand) : laplacian F w = 0 := by
  obtain ⟨hN1, hNlt, -, -, -⟩ := frame.child_facts
  obtain ⟨-, hwin⟩ := (frame.mem_hBand_iff w).mp hw
  have hz := hstrips.1
  unfold laplacian
  by_cases he : EvenSite w
  · rw [if_pos he] at hwin
    simp only [incomingNeg, incomingPos, if_pos he]
    have h0 : F w = 0 := hz w (by omega) (by omega)
    have h1 : F (w.1 - 1, w.2) = 0 :=
      hz _ (by rw [frame.tGrade_sub_x w]; omega) (by rw [frame.tGrade_sub_x w]; omega)
    have h2 : F (w.1 + 1, w.2) = 0 :=
      hz _ (by rw [frame.tGrade_add_x w]; omega) (by rw [frame.tGrade_add_x w]; omega)
    simp [h0, h1, h2]
  · rw [if_neg he] at hwin
    simp only [incomingNeg, incomingPos, if_neg he]
    have h0 : F w = 0 := hz w (by omega) (by omega)
    have h1 : F (w.1, w.2 - 1) = 0 :=
      hz _ (by rw [frame.tGrade_sub_y w]; omega) (by rw [frame.tGrade_sub_y w]; omega)
    have h2 : F (w.1, w.2 + 1) = 0 :=
      hz _ (by rw [frame.tGrade_add_y w]; omega) (by rw [frame.tGrade_add_y w]; omega)
    simp [h0, h1, h2]

/-- At a site of the vertical band the harmonic strip contains the site and both its inputs. -/
theorem ChildFrame.laplacian_eq_zero_of_vBand (frame : ChildFrame) {F : Field}
    (hstrips : frame.HasStrips F) {w : Site} (hw : w ∈ frame.vBand) : laplacian F w = 0 := by
  obtain ⟨hN1, hNlt, -, -, -⟩ := frame.child_facts
  obtain ⟨-, hwin⟩ := (frame.mem_vBand_iff w).mp hw
  have hh := hstrips.2
  have hlap := harmonicGrid_harmonic w
  unfold laplacian at hlap ⊢
  by_cases he : EvenSite w
  · rw [if_pos he] at hwin
    simp only [incomingNeg, incomingPos, if_pos he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1 - 1, w.2) = harmonicGrid (w.1 - 1, w.2) :=
      hh _ (by rw [frame.sGrade_sub_x w]; omega) (by rw [frame.sGrade_sub_x w]; omega)
    have h2 : F (w.1 + 1, w.2) = harmonicGrid (w.1 + 1, w.2) :=
      hh _ (by rw [frame.sGrade_add_x w]; omega) (by rw [frame.sGrade_add_x w]; omega)
    rw [h0, h1, h2]
    linarith
  · rw [if_neg he] at hwin
    simp only [incomingNeg, incomingPos, if_neg he] at hlap ⊢
    have h0 : F w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : F (w.1, w.2 - 1) = harmonicGrid (w.1, w.2 - 1) :=
      hh _ (by rw [frame.sGrade_sub_y w]; omega) (by rw [frame.sGrade_sub_y w]; omega)
    have h2 : F (w.1, w.2 + 1) = harmonicGrid (w.1, w.2 + 1) :=
      hh _ (by rw [frame.sGrade_add_y w]; omega) (by rw [frame.sGrade_add_y w]; omega)
    rw [h0, h1, h2]
    linarith

/-- The sewn standard is binary: its Laplacian takes only the values `-1` and `0`. -/
theorem ChildFrame.binary_of_strips (frame : ChildFrame) {F M : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hagree : ∀ z ∈ frame.closedPolygon, F z = M z)
    (hM : ∀ z ∈ frame.closedPolygon, laplacian M z = -1 ∨ laplacian M z = 0)
    (hstrips : frame.HasStrips F)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) :
    ∀ z, laplacian F z = -1 ∨ laplacian F z = 0 := by
  refine frame.laplacian_forall_of_closedPolygon hper (fun v => v = -1 ∨ v = 0) ?_
  intro z hz
  show laplacian F z = -1 ∨ laplacian F z = 0
  by_cases hin : incomingNeg z ∈ frame.closedPolygon ∧ incomingPos z ∈ frame.closedPolygon
  · have hF : laplacian F z = laplacian M z := by
      unfold laplacian
      rw [hagree _ hin.1, hagree _ hin.2, hagree _ hz]
    rw [hF]
    exact hM z hz
  · have hbad : ∃ u, Edge u z ∧ u ∉ frame.closedPolygon := by
      by_cases hN : incomingNeg z ∈ frame.closedPolygon
      · exact ⟨incomingPos z, Or.inr rfl, fun hP => hin ⟨hN, hP⟩⟩
      · exact ⟨incomingNeg z, Or.inl rfl, hN⟩
    obtain ⟨u, hu, hout⟩ := hbad
    rcases frame.mem_bands_of_input_not_mem hz hu hout with h | h | h | h
    · exact Or.inr (frame.laplacian_eq_zero_of_hBand hstrips h)
    · exact Or.inr (frame.laplacian_eq_zero_of_vBand hstrips h)
    · exact Or.inr ((frame.laplacian_centre_sub hrefl z).symm.trans
        (frame.laplacian_eq_zero_of_hBand hstrips h))
    · exact Or.inr ((frame.laplacian_centre_sub hrefl z).symm.trans
        (frame.laplacian_eq_zero_of_vBand hstrips h))

end FLatticePaper.Induction
