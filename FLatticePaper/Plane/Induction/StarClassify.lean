import FLatticePaper.Plane.Induction.StrongUnitPrice
import FLatticePaper.Plane.Induction.StarCover
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.BothFreeGrades

/-!
# The full-star classification `StarClassified` from the grade covering (STRONG_PRICE §3)

`starClassified_of_grades`: for a child frame with odd numerator and denominator, `3 ≤ num` and `num + 4 ≤ den`, and a strip
`HasStrips F`, every star is classified after one deck translate (`StarClassified`). The proof transports the grade covering
`StarCover.box_cover` to the sites: the deck vector `deckVec i j` shifts the grades by `(−jT, iT)` (`T` the period denominator), the
incoming sites shift the grades by `(∓num, ∓(den+num))` at an even centre and `(±den, ∓(den−num))` at an odd one, and a site whose grades
lie in the covering set is in the closed polygon, in the H-band, or a V source (`kind_of_ok`, with the strip for V).
-/

namespace FLatticePaper.StrongUnitPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.StrongHSpan

section Grades

variable (frame : ChildFrame)

theorem kernel_eq (hpar : (frame.child.num + frame.child.den) % 2 = 0) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hpar]

theorem transverse_eq :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

/-- The `t`-grade of a deck translate: the kernel contributes nothing, the transverse vector `−T`. -/
theorem tGrade_add_deck (hpar : (frame.child.num + frame.child.den) % 2 = 0) (z : Site) (i j : ℤ) :
    frame.tGrade (z + deckVec frame i j) = frame.tGrade z - j * frame.child.periodDenominator := by
  simp only [ChildFrame.tGrade, deckVec, kernel_eq frame hpar, transverse_eq frame, Prod.fst_add, Prod.snd_add,
    Fraction.periodDenominator]
  ring

/-- The `s`-grade of a deck translate: the kernel contributes `T`, the transverse vector nothing. -/
theorem sGrade_add_deck (hpar : (frame.child.num + frame.child.den) % 2 = 0) (z : Site) (i j : ℤ) :
    frame.sGrade (z + deckVec frame i j) = frame.sGrade z + i * frame.child.periodDenominator := by
  simp only [ChildFrame.sGrade, deckVec, kernel_eq frame hpar, transverse_eq frame, Prod.fst_add, Prod.snd_add,
    Fraction.periodDenominator]
  ring

theorem tGrade_incomingNeg_even (z : Site) (hz : EvenSite z) :
    frame.tGrade (FLatticePaper.incomingNeg z) = frame.tGrade z - frame.child.num := by
  unfold FLatticePaper.incomingNeg
  rw [if_pos hz]
  unfold ChildFrame.tGrade
  ring

theorem tGrade_incomingNeg_odd (z : Site) (hz : ¬ EvenSite z) :
    frame.tGrade (FLatticePaper.incomingNeg z) = frame.tGrade z + frame.child.den := by
  unfold FLatticePaper.incomingNeg
  rw [if_neg hz]
  unfold ChildFrame.tGrade
  ring

theorem sGrade_incomingNeg_even (z : Site) (hz : EvenSite z) :
    frame.sGrade (FLatticePaper.incomingNeg z) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold FLatticePaper.incomingNeg
  rw [if_pos hz]
  unfold ChildFrame.sGrade
  ring

theorem sGrade_incomingNeg_odd (z : Site) (hz : ¬ EvenSite z) :
    frame.sGrade (FLatticePaper.incomingNeg z) = frame.sGrade z - (frame.child.den - frame.child.num) := by
  unfold FLatticePaper.incomingNeg
  rw [if_neg hz]
  unfold ChildFrame.sGrade
  ring

theorem tGrade_incomingPos_even (z : Site) (hz : EvenSite z) :
    frame.tGrade (FLatticePaper.incomingPos z) = frame.tGrade z + frame.child.num := by
  unfold FLatticePaper.incomingPos
  rw [if_pos hz]
  unfold ChildFrame.tGrade
  ring

theorem tGrade_incomingPos_odd (z : Site) (hz : ¬ EvenSite z) :
    frame.tGrade (FLatticePaper.incomingPos z) = frame.tGrade z - frame.child.den := by
  unfold FLatticePaper.incomingPos
  rw [if_neg hz]
  unfold ChildFrame.tGrade
  ring

theorem sGrade_incomingPos_even (z : Site) (hz : EvenSite z) :
    frame.sGrade (FLatticePaper.incomingPos z) = frame.sGrade z + (frame.child.den + frame.child.num) := by
  unfold FLatticePaper.incomingPos
  rw [if_pos hz]
  unfold ChildFrame.sGrade
  ring

theorem sGrade_incomingPos_odd (z : Site) (hz : ¬ EvenSite z) :
    frame.sGrade (FLatticePaper.incomingPos z) = frame.sGrade z + (frame.child.den - frame.child.num) := by
  unfold FLatticePaper.incomingPos
  rw [if_neg hz]
  unfold ChildFrame.sGrade
  ring

/-- The parity of a site is the parity of its `t`-grade (the numerator and denominator are odd). -/
theorem even_iff_tGrade (a b : ℤ) (ha : frame.child.num = 2 * a + 1) (hb : frame.child.den = 2 * b + 1) (z : Site) :
    EvenSite z ↔ frame.tGrade z % 2 = 0 := by
  have key : frame.tGrade z = 2 * (a * z.1 - b * z.2) + (z.1 - z.2) := by
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  unfold EvenSite
  rw [key]
  omega

/-- The `s`-grade is even (both `den + num` and `den − num` are even). -/
theorem sGrade_even_of (a b : ℤ) (ha : frame.child.num = 2 * a + 1) (hb : frame.child.den = 2 * b + 1) (z : Site) :
    frame.sGrade z % 2 = 0 := by
  have key : frame.sGrade z = 2 * ((a + b + 1) * z.1 + (b - a) * z.2) := by
    unfold ChildFrame.sGrade
    rw [ha, hb]
    ring
  rw [key]
  omega

/-- The period denominator is even. -/
theorem periodDenominator_even_of (a b : ℤ) (ha : frame.child.num = 2 * a + 1) (hb : frame.child.den = 2 * b + 1) :
    frame.child.periodDenominator % 2 = 0 := by
  have key : frame.child.periodDenominator = 2 * (2 * b ^ 2 + 4 * b + 4 * a * b - 2 * a ^ 2 + 1) := by
    unfold Fraction.periodDenominator
    rw [ha, hb]
    ring
  rw [key]
  simp [Int.mul_emod_right]

/-- The strip gives the V sources: `F` is harmonic on the strip `3 − 2d ≤ s ≤ 2(d + n) − 1` (with the parent shift). -/
theorem kind_of_ok (F : Field) (hstrips : frame.HasStrips F) (a b : ℤ) (ha : frame.child.num = 2 * a + 1)
    (hb : frame.child.den = 2 * b + 1) (z : Site)
    (h : StarCover.OkSite frame.child.num frame.child.den frame.child.periodDenominator (frame.tGrade z) (frame.sGrade z)) :
    z ∈ frame.closedPolygon ∨ HStarBand frame z ∨ VSource frame F z := by
  have hev := even_iff_tGrade frame a b ha hb z
  unfold StarCover.OkSite at h
  rcases h with ⟨ht, h1, h2, h3, h4⟩ | ⟨ht, h1, h2, h3, h4⟩ | ⟨ht, h1, h2⟩ | ⟨ht, h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [frame.mem_closedPolygon_iff]
    exact Or.inl ⟨hev.2 ht, h1, h2, h3, h4⟩
  · left
    rw [frame.mem_closedPolygon_iff]
    exact Or.inr ⟨fun he => by have := hev.1 he; omega, h1, h2, h3, h4⟩
  · right; left
    unfold HStarBand
    exact ⟨fun _ => ⟨h1, h2⟩, fun hn => absurd (hev.2 ht) hn⟩
  · right; left
    unfold HStarBand
    exact ⟨fun he => absurd (hev.1 he) (by omega), fun _ => ⟨h1, h2⟩⟩
  · right; right
    have hv : frame.sGrade (z - frame.parentShift) = frame.sGrade z - 2 := by
      rw [BothFreeGrades.sGrade_sub, BothFreeGrades.sGrade_parentShift]
    unfold VSource
    exact ⟨hstrips.2 z (by omega) (by omega), hstrips.2 (z - frame.parentShift) (by rw [hv]; omega) (by rw [hv]; omega)⟩

end Grades

/-- **`StarClassified` for a proper child.** Every star is classified after one deck translate: the translate brings the centre into
the box `[0, T) × [0, T)` (the `t`-grade by `j = t / T`, the `s`-grade by `i = −(s / T)`), and then the covering `box_cover` applies. -/
theorem starClassified_of_grades (frame : ChildFrame) (F : Field) (hn3 : 3 ≤ frame.child.num) (hd4 : 4 ≤ frame.child.den - frame.child.num)
    (hstrips : frame.HasStrips F) : StarClassified frame F := by
  obtain ⟨a, b, ha, hb⟩ := PriceDeck.child_odd_witness frame
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := by omega
  have hTe : frame.child.periodDenominator % 2 = 0 := periodDenominator_even_of frame a b ha hb
  have hTdef : frame.child.periodDenominator =
      frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hTb : 2 * frame.child.den + 2 * frame.child.num ≤ frame.child.periodDenominator := by
    rw [hTdef]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 4 by omega)
      (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.num by omega)]
  have hTpos : 0 < frame.child.periodDenominator := by
    have : (0 : ℤ) < frame.child.den := by omega
    have : (0 : ℤ) < frame.child.num := by omega
    omega
  have hdvd : (2 : ℤ) ∣ frame.child.periodDenominator := Int.dvd_of_emod_eq_zero hTe
  have hno : frame.child.num % 2 = 1 := by omega
  have hdo : frame.child.den % 2 = 1 := by omega
  intro c
  have hcpar := even_iff_tGrade frame a b ha hb c
  have hs2 : frame.sGrade c % 2 = 0 := sGrade_even_of frame a b ha hb c
  -- the box point of `c`
  have hmodT : frame.tGrade c % frame.child.periodDenominator
      = frame.tGrade c - frame.child.periodDenominator * (frame.tGrade c / frame.child.periodDenominator) :=
    Int.emod_def _ _
  have hmodS : frame.sGrade c % frame.child.periodDenominator
      = frame.sGrade c - frame.child.periodDenominator * (frame.sGrade c / frame.child.periodDenominator) :=
    Int.emod_def _ _
  have hpt : frame.tGrade c % frame.child.periodDenominator % 2 = frame.tGrade c % 2 :=
    Int.emod_emod_of_dvd _ hdvd
  have hps : frame.sGrade c % frame.child.periodDenominator % 2 = 0 := by
    rw [Int.emod_emod_of_dvd _ hdvd]
    exact hs2
  have hlo : 0 ≤ frame.tGrade c % frame.child.periodDenominator := Int.emod_nonneg _ hTpos.ne'
  have hhi : frame.tGrade c % frame.child.periodDenominator < frame.child.periodDenominator :=
    Int.emod_lt_of_pos _ hTpos
  have hslo : 0 ≤ frame.sGrade c % frame.child.periodDenominator := Int.emod_nonneg _ hTpos.ne'
  have hshi : frame.sGrade c % frame.child.periodDenominator < frame.child.periodDenominator :=
    Int.emod_lt_of_pos _ hTpos
  have hcover := StarCover.box_cover frame.child.num frame.child.den frame.child.periodDenominator
    (frame.tGrade c % frame.child.periodDenominator) (frame.sGrade c % frame.child.periodDenominator)
    hno hdo hn3 (by omega) hTb hTe hlo hhi hslo hshi hps
  rcases hcover with ⟨hpe, h1, h2, h3⟩ | ⟨hpo, hband, -, h1, h2, h3⟩ | ⟨hpo, -, h1, h2, h3⟩
  · -- the box point is even: the translate `t ↦ t − T`
    have hev : EvenSite c := (hcpar).2 (by omega)
    refine ⟨-(frame.sGrade c / frame.child.periodDenominator), frame.tGrade c / frame.child.periodDenominator + 1, ?_⟩
    rintro x (rfl | rfl | rfl)
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar]
      rw [show frame.tGrade x - (frame.tGrade x / frame.child.periodDenominator + 1) * frame.child.periodDenominator
          = frame.tGrade x % frame.child.periodDenominator - frame.child.periodDenominator by rw [hmodT]; ring,
        show frame.sGrade x + -(frame.sGrade x / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade x % frame.child.periodDenominator by rw [hmodS]; ring]
      exact h1
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingNeg_even frame c hev,
        sGrade_incomingNeg_even frame c hev]
      rw [show frame.tGrade c - frame.child.num - (frame.tGrade c / frame.child.periodDenominator + 1) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            - frame.child.num by rw [hmodT]; ring,
        show frame.sGrade c - (frame.child.den + frame.child.num) +
          -(frame.sGrade c / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator - (frame.child.den + frame.child.num) by rw [hmodS]; ring]
      exact h2
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingPos_even frame c hev,
        sGrade_incomingPos_even frame c hev]
      rw [show frame.tGrade c + frame.child.num - (frame.tGrade c / frame.child.periodDenominator + 1) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            + frame.child.num by rw [hmodT]; ring,
        show frame.sGrade c + (frame.child.den + frame.child.num) +
          -(frame.sGrade c / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator + (frame.child.den + frame.child.num) by rw [hmodS]; ring]
      exact h3
  · -- the box point is odd and in the band: the translate `(t, s) ↦ (t + 2T, s − T)`
    have hodd : ¬ EvenSite c := fun h => by have := hcpar.1 h; omega
    refine ⟨-(frame.sGrade c / frame.child.periodDenominator) - 1, frame.tGrade c / frame.child.periodDenominator - 2, ?_⟩
    rintro x (rfl | rfl | rfl)
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar]
      rw [show frame.tGrade x - (frame.tGrade x / frame.child.periodDenominator - 2) * frame.child.periodDenominator
          = frame.tGrade x % frame.child.periodDenominator + 2 * frame.child.periodDenominator by rw [hmodT]; ring,
        show frame.sGrade x + (-(frame.sGrade x / frame.child.periodDenominator) - 1) * frame.child.periodDenominator
          = frame.sGrade x % frame.child.periodDenominator - frame.child.periodDenominator by rw [hmodS]; ring]
      exact h1
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingNeg_odd frame c hodd,
        sGrade_incomingNeg_odd frame c hodd]
      rw [show frame.tGrade c + frame.child.den - (frame.tGrade c / frame.child.periodDenominator - 2) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator + 2 * frame.child.periodDenominator
            + frame.child.den by rw [hmodT]; ring,
        show frame.sGrade c - (frame.child.den - frame.child.num) +
          (-(frame.sGrade c / frame.child.periodDenominator) - 1) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            - (frame.child.den - frame.child.num) by rw [hmodS]; ring]
      exact h2
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingPos_odd frame c hodd,
        sGrade_incomingPos_odd frame c hodd]
      rw [show frame.tGrade c - frame.child.den - (frame.tGrade c / frame.child.periodDenominator - 2) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator + 2 * frame.child.periodDenominator
            - frame.child.den by rw [hmodT]; ring,
        show frame.sGrade c + (frame.child.den - frame.child.num) +
          (-(frame.sGrade c / frame.child.periodDenominator) - 1) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            + (frame.child.den - frame.child.num) by rw [hmodS]; ring]
      exact h3
  · -- the box point is odd and outside the band: the translate `t ↦ t − T`
    have hodd : ¬ EvenSite c := fun h => by have := hcpar.1 h; omega
    refine ⟨-(frame.sGrade c / frame.child.periodDenominator), frame.tGrade c / frame.child.periodDenominator + 1, ?_⟩
    rintro x (rfl | rfl | rfl)
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar]
      rw [show frame.tGrade x - (frame.tGrade x / frame.child.periodDenominator + 1) * frame.child.periodDenominator
          = frame.tGrade x % frame.child.periodDenominator - frame.child.periodDenominator by rw [hmodT]; ring,
        show frame.sGrade x + -(frame.sGrade x / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade x % frame.child.periodDenominator by rw [hmodS]; ring]
      exact h1
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingNeg_odd frame c hodd,
        sGrade_incomingNeg_odd frame c hodd]
      rw [show frame.tGrade c + frame.child.den - (frame.tGrade c / frame.child.periodDenominator + 1) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            + frame.child.den by rw [hmodT]; ring,
        show frame.sGrade c - (frame.child.den - frame.child.num) +
          -(frame.sGrade c / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator - (frame.child.den - frame.child.num) by rw [hmodS]; ring]
      exact h2
    · refine kind_of_ok frame F hstrips a b ha hb _ ?_
      rw [tGrade_add_deck frame hpar, sGrade_add_deck frame hpar, tGrade_incomingPos_odd frame c hodd,
        sGrade_incomingPos_odd frame c hodd]
      rw [show frame.tGrade c - frame.child.den - (frame.tGrade c / frame.child.periodDenominator + 1) *
          frame.child.periodDenominator = frame.tGrade c % frame.child.periodDenominator - frame.child.periodDenominator
            - frame.child.den by rw [hmodT]; ring,
        show frame.sGrade c + (frame.child.den - frame.child.num) +
          -(frame.sGrade c / frame.child.periodDenominator) * frame.child.periodDenominator
          = frame.sGrade c % frame.child.periodDenominator + (frame.child.den - frame.child.num) by rw [hmodS]; ring]
      exact h3

end FLatticePaper.StrongUnitPrice
