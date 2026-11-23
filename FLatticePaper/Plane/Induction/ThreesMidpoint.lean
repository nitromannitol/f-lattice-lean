import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Construction.AlternateStaircaseExtension
import FLatticePaper.Plane.Induction.TwosReciprocal

namespace FLatticePaper.Induction.ThreesMidpoint

/-! Task 53 (hbaseThree), step 1: the explicit reciprocal reduction. For the reciprocal field `R` of `3^k` (child `1/d`,
`d = 2k+3`), `2 R(y + i U + j V) = 2 stairEvenValue(y) + 2j(y1 - d y2 + c) - T j (j-1)` for `y` in the stair tile.
Here the second difference `D2(z) = R(z+e1) + R(z-e1) - 2 R z` takes the values -1, 0, 1, and `D2 = 1` exactly where the
alternate marker `stairEvenAltMarker` fires at `z + e1` (the inner diagonal `x1 + x2 = 2`, `1 ≤ x2 ≤ d-1`). This file
collects the tile tables, the marker lemmas and the reduction bridge; the nine neighbour cases follow in the next step. -/

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

/-- The reciprocal deck translate `i U + j V` of `1/d`, with `U = (d,1)` and `V = (1-d,1+d)`. -/
def thr (d i j : ℤ) : Site := (i * d + j * (1 - d), i + j * (1 + d))

theorem thr_add (d a b i j : ℤ) : thr d (a + i) (b + j) = thr d a b + thr d i j :=
  Prod.ext (by simp only [thr, Prod.fst_add]; ring) (by simp only [thr, Prod.snd_add]; ring)

/-- Twice the stair value of the tile, without division. -/
def Mt (d : ℤ) (p : Site) : ℤ :=
  -(p.2 * (p.2 - 1)) + 2 * min (p.1 - 1) 0 + 2 * (if BaseMask.StairEvenCorner d p then 1 else 0)

theorem two_mul_stairEvenValue (d : ℤ) (p : Site) : 2 * BaseMask.stairEvenValue d p = Mt d p := by
  have h2 : (2 : ℤ) ∣ p.2 * (p.2 - 1) := (Int.even_mul_pred_self p.2).two_dvd
  have hdiv := Int.mul_ediv_cancel' h2
  unfold BaseMask.stairEvenValue Mt
  linarith

theorem period_eq (d : ℤ) : (Fraction.mk 1 d).periodDenominator = d ^ 2 + 2 * d - 1 := by
  simp only [Fraction.periodDenominator]; ring

/-- The alternate marker is invariant under the reciprocal deck. -/
theorem marker_thr (d : ℤ) (x : Site) (i j : ℤ) :
    stairEvenAltMarker d (x + thr d i j) = stairEvenAltMarker d x := by
  have hlev : staircaseLevel d (x + thr d i j) = staircaseLevel d x - j * (d ^ 2 + 2 * d - 1) := by
    simp only [staircaseLevel, thr, Prod.fst_add, Prod.snd_add]; ring
  have hmod : ∀ L : ℤ, (L - j * (d ^ 2 + 2 * d - 1)) % (d ^ 2 + 2 * d - 1) = L % (d ^ 2 + 2 * d - 1) := by
    intro L; rw [Int.sub_emod, Int.mul_emod_left, sub_zero, Int.emod_emod]
  unfold stairEvenAltMarker
  simp only [period_eq, hlev, hmod]

/-- On the tile, the alternate marker is the indicator of the inner diagonal `x1 + x2 = 2`, `1 ≤ x2 ≤ d-1`. -/
theorem marker_tile (d : ℤ) (hd : 3 ≤ d) (q : Site) (hq : q ∈ (BaseMask.stairEven.raw d).sites) :
    stairEvenAltMarker d q = if q.1 + q.2 = 2 ∧ 1 ≤ q.2 ∧ q.2 ≤ d - 1 then 1 else 0 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := BaseMask.mem_stairEven_raw_iff.mp hq
  unfold BaseMask.StairEvenCorner at h5
  unfold stairEvenAltMarker
  simp only [period_eq]
  by_cases hdiag : q.1 + q.2 = 2 ∧ 1 ≤ q.2 ∧ q.2 ≤ d - 1
  · rw [if_pos hdiag, if_pos]
    refine ⟨q.2, Finset.mem_Ico.mpr ⟨hdiag.2.1, by omega⟩, ?_⟩
    have hq1 : q.1 = 2 - q.2 := by omega
    congr 1
    simp only [staircaseLevel, hq1]
    ring
  · rw [if_neg hdiag, if_neg]
    rintro ⟨row, hrow, heq⟩
    rw [Finset.mem_Ico] at hrow
    have hm : Int.ModEq (d ^ 2 + 2 * d - 1) (staircaseLevel d q) (2 - (d + 1) * row) := heq
    obtain ⟨c, hc⟩ := hm.dvd
    simp only [staircaseLevel] at hc
    have hXb1 : d * q.2 ≤ d * (d + 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hXb2 : (d + 1) * row ≤ (d + 1) * (d - 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hXb3 : 0 ≤ d * q.2 := mul_nonneg (by omega) h3
    have hXb4 : (d + 1) * 1 ≤ (d + 1) * row := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hT : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
    have hc0 : c = 0 := by
      rcases lt_trichotomy c 0 with hc' | hc' | hc'
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ -c - 1 by omega) hT]
      · exact hc'
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ c - 1 by omega) hT]
    subst hc0
    have hX : q.1 + q.2 - 2 = (d + 1) * (q.2 - row) := by linear_combination (-1 : ℤ) * hc
    rcases (show q.2 - row ≤ -1 ∨ q.2 - row = 0 ∨ q.2 - row = 1 ∨ 2 ≤ q.2 - row by omega) with hm1 | hm0 | hm1 | hm2
    · have : (d + 1) * (q.2 - row) ≤ -(d + 1) := by nlinarith
      omega
    · rw [hm0, mul_zero] at hX
      exact hdiag ⟨by omega, by omega, by omega⟩
    · rw [hm1, mul_one] at hX
      omega
    · have : 2 * (d + 1) ≤ (d + 1) * (q.2 - row) := by nlinarith
      omega


theorem mem_TS_iff (d : ℤ) (p : Site) : p ∈ (BaseMask.stairEven.raw d).sites ↔
    (2 - d ≤ p.1 ∧ p.1 ≤ d) ∧ (0 ≤ p.2 ∧ p.2 ≤ d + 1) ∧
      ((p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = 2 ∧ p.2 = d + 1) ∨ (1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ d + 2)) := by
  rw [BaseMask.mem_stairEven_raw_iff]
  simp only [BaseMask.StairEvenCorner, or_assoc]

/-- Every `y + e1` lies in the tile after at most one deck step (`K0`, `K1`, `K2`). -/
theorem plus_table (d : ℤ) (hd : 3 ≤ d) (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) :
    (y.1 + 1, y.2) ∈ (BaseMask.stairEven.raw d).sites ∨
    (y.1 + 1 - d, y.2 - 1) ∈ (BaseMask.stairEven.raw d).sites ∨
    (y.1 + 2 - d, y.2 + d + 1) ∈ (BaseMask.stairEven.raw d).sites := by
  simp only [mem_TS_iff] at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  omega

/-- Every `y - e1` lies in the tile after at most one deck step (`L0`, `L1`, `L2`). -/
theorem minus_table (d : ℤ) (hd : 3 ≤ d) (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) :
    (y.1 - 1, y.2) ∈ (BaseMask.stairEven.raw d).sites ∨
    (y.1 - 1 + d, y.2 + 1) ∈ (BaseMask.stairEven.raw d).sites ∨
    (y.1 - 2 + 2 * d, y.2 - d) ∈ (BaseMask.stairEven.raw d).sites := by
  simp only [mem_TS_iff] at hy ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hy
  omega

theorem combine_eq_thr (d : ℤ) (hodd : d % 2 = 1) (i j : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine i j = thr d i j := by
  have heven : (1 + d) % 2 = 0 := by omega
  simp [PeriodDeck.combine, Fraction.modifiedDeck, Fraction.periodMultiplicity, Fraction.unmodifiedDeck,
    heven, thr]

theorem stair_cover (d : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (z : Site) :
    ∃ y ∈ (BaseMask.stairEven.raw d).sites, ∃ a b : ℤ, z = y + thr d a b := by
  obtain ⟨y, hy, hspan⟩ := stairEven_raw_cover (show BaseMask.stairEven.Valid d from ⟨hd, hodd⟩) z
  rw [reciprocalEvenDeck_eq hodd] at hspan
  simp only [PeriodDeck.span, Set.mem_setOf_eq] at hspan
  obtain ⟨a, b, hab⟩ := hspan
  refine ⟨y, hy, a, b, ?_⟩
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  simp only [PeriodDeck.combine, Prod.fst_sub, Prod.snd_sub] at h1 h2
  apply Prod.ext
  · simp only [thr, Prod.fst_add]; linarith
  · simp only [thr, Prod.snd_add]; linarith

theorem stairEvenConstantV_twice (d : ℤ) (hodd : d % 2 = 1) :
    2 * stairEvenConstantV d = -d ^ 2 - 3 * d := by
  have h2 : (2 : ℤ) ∣ d * (d + 3) := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.mul_emod]
    have : (d + 3) % 2 = 0 := by omega
    simp [this]
  have hdiv := Int.mul_ediv_cancel' h2
  rw [stairEvenConstantV_eq]
  linear_combination (-1 : ℤ) * hdiv

/-- The explicit reduction of the reciprocal field, in the coordinates of `thr`. -/
theorem reciprocal_hred (k : ℕ) (y : Site) (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (i j : ℤ) :
    2 * reciprocalField k (y + thr (2 * (k : ℤ) + 3) i j) =
      Mt (2 * (k : ℤ) + 3) y + 2 * j * (y.1 - (2 * (k : ℤ) + 3) * y.2 + stairEvenConstantV (2 * (k : ℤ) + 3)) -
        ((2 * (k : ℤ) + 3) ^ 2 + 2 * (2 * (k : ℤ) + 3) - 1) * j * (j - 1) := by
  have hodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have h := reciprocalField_reduction k hy (z := y + thr (2 * (k : ℤ) + 3) i j) (i := i) (j := j)
    (by rw [combine_eq_thr _ hodd])
  rw [two_mul_stairEvenValue, period_eq] at h
  have htg : (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade y = (2 * (k : ℤ) + 3) * y.2 - y.1 := by
    simp [Fraction.transverseGrade]
  rw [htg] at h
  linear_combination h


/-- The second difference along `e1` in one neighbour configuration: `2 D2` is the tile increment plus the deck correction. -/
theorem combo_identity (d c : ℤ) (RF : Site → ℤ)
    (hred : ∀ (y : Site) (i j : ℤ), y ∈ (BaseMask.stairEven.raw d).sites →
      2 * RF (y + thr d i j) = Mt d y + 2 * j * (y.1 - d * y.2 + c) - (d ^ 2 + 2 * d - 1) * j * (j - 1))
    (y : Site) (hy : y ∈ (BaseMask.stairEven.raw d).sites) (a b ip jp im jm : ℤ) (qp qm : Site)
    (hqp : qp ∈ (BaseMask.stairEven.raw d).sites) (hqm : qm ∈ (BaseMask.stairEven.raw d).sites)
    (eqp : qp = (y.1 + 1, y.2) - thr d ip jp) (eqm : qm = (y.1 - 1, y.2) - thr d im jm) :
    2 * (RF (y + thr d a b + (1, 0)) + RF (y + thr d a b - (1, 0)) - 2 * RF (y + thr d a b)) =
        Mt d qp + Mt d qm - 2 * Mt d y +
          (2 * (y.1 - d * y.2 + c) * (jp + jm) + 2 * (jp - jm) +
            (d ^ 2 + 2 * d - 1) * (jp ^ 2 + jm ^ 2 + jp + jm)) ∧
      stairEvenAltMarker d (y + thr d a b + (1, 0)) = stairEvenAltMarker d qp := by
  subst eqp eqm
  have e1 : y + thr d a b + (1, 0) = ((y.1 + 1, y.2) - thr d ip jp) + thr d (a + ip) (b + jp) :=
    Prod.ext (by simp only [thr, Prod.fst_add, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_add, Prod.snd_sub]; ring)
  have e2 : y + thr d a b - (1, 0) = ((y.1 - 1, y.2) - thr d im jm) + thr d (a + im) (b + jm) :=
    Prod.ext (by simp only [thr, Prod.fst_add, Prod.fst_sub]; ring) (by simp only [thr, Prod.snd_add, Prod.snd_sub]; ring)
  have h1 := hred _ (a + ip) (b + jp) hqp
  have h2 := hred _ (a + im) (b + jm) hqm
  have h0 := hred y a b hy
  refine ⟨?_, ?_⟩
  · rw [e1, e2]
    simp only [thr, Prod.fst_sub, Prod.snd_sub] at h1 h2 h0 ⊢
    linear_combination h1 + h2 - 2 * h0
  · rw [e1, marker_thr]

end FLatticePaper.Induction.ThreesMidpoint
