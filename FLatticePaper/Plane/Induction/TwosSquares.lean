import FLatticePaper.Plane.Induction.TwosQuota
import FLatticePaper.Plane.Induction.TwosLaplacianTile

/-! The squares of the twos signed policy (task 72): the free classes on the native box, and the square clause. A native point
`w` lies in a free class exactly when `w` itself, `w - V` or `w - U` is an H or V site: a free alias `w - (i U + l V)` of a native
point forces `(i, l) ∈ {(0,0), (0,1), (1,0)}` (`alias_bounds`, then a case analysis). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The coefficients of a difference `p - q = I U + L V` of a native point `p` and a free point `q` are bounded. -/
theorem alias_bounds {a I L p1 p2 q1 q2 : ℤ} (ha : 4 ≤ a) (hp1 : -1 ≤ p1) (hp1' : p1 ≤ a + 1) (hp2 : 0 ≤ p2)
    (hp2' : p2 ≤ 3 * a - 2) (hq1 : -1 ≤ q1) (hq1' : q1 ≤ a + 1) (hq2 : 0 ≤ q2) (hq2' : q2 ≤ 2 * a - 1)
    (hD1 : p1 - q1 = I * (a + 1) - 2 * L) (hD2 : p2 - q2 = I * (a - 1) + 2 * a * L) :
    -1 ≤ I ∧ I ≤ 1 ∧ -1 ≤ L ∧ L ≤ 1 := by
  have hT : I * (2 * a * a + 4 * a - 2) = 2 * a * (p1 - q1) + 2 * (p2 - q2) := by
    rw [hD1, hD2]
    ring
  have hT0 : 0 < 2 * a * a + 4 * a - 2 := by nlinarith
  have hI1 : I ≤ 1 := by
    by_contra hc
    have h1 : 2 * (2 * a * a + 4 * a - 2) ≤ I * (2 * a * a + 4 * a - 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    have h2 : 2 * a * (p1 - q1) ≤ 2 * a * (a + 2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  have hI2 : -1 ≤ I := by
    by_contra hc
    have h1 : I * (2 * a * a + 4 * a - 2) ≤ -2 * (2 * a * a + 4 * a - 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    have h2 : 2 * a * (-(a + 2)) ≤ 2 * a * (p1 - q1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  have hL1 : L ≤ 1 := by
    by_contra hc
    have h1 : 2 * a * 2 ≤ 2 * a * L := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : (-1) * (a - 1) ≤ I * (a - 1) := mul_le_mul_of_nonneg_right hI2 (by omega)
    nlinarith
  have hL2 : -1 ≤ L := by
    by_contra hc
    have h1 : 2 * a * L ≤ 2 * a * (-2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : I * (a - 1) ≤ 1 * (a - 1) := mul_le_mul_of_nonneg_right hI1 (by omega)
    nlinarith
  exact ⟨hI2, hI1, hL2, hL1⟩

/-- A free alias of a native point is one of `w`, `w - V`, `w - U` (the coefficients are `(0,0)`, `(0,1)`, `(1,0)`). -/
theorem native_free_alias {a i l : ℤ} (ha : 4 ≤ a) {w u : Site} (hw : NativeT a w.1 w.2)
    (hu : FreeSite a u.1 u.2) (hl : u = (w.1 - i * (a + 1) + 2 * l, w.2 - i * (a - 1) - 2 * a * l)) :
    (i = 0 ∧ l = 0) ∨ (i = 0 ∧ l = 1) ∨ (i = 1 ∧ l = 0) := by
  obtain ⟨hp1, hp1', hp2, hp2'⟩ : -1 ≤ w.1 ∧ w.1 ≤ a + 1 ∧ 0 ≤ w.2 ∧ w.2 ≤ 3 * a - 2 := by
    simp only [NativeT] at hw
    omega
  obtain ⟨q1, q2⟩ := u
  simp only [FreeSite, FreeHSite, FreeVSite] at hu
  simp only [Prod.mk.injEq] at hl
  obtain ⟨hl1, hl2⟩ := hl
  have hq : -1 ≤ q1 ∧ q1 ≤ a + 1 ∧ 0 ≤ q2 ∧ q2 ≤ 2 * a - 1 := by
    omega
  obtain ⟨hq1, hq1', hq2, hq2'⟩ := hq
  have hb := alias_bounds ha hp1 hp1' hp2 hp2' hq1 hq1' hq2 hq2'
    (I := i) (L := l) (by rw [hl1]; ring) (by rw [hl2]; ring)
  obtain ⟨hI1, hI2, hL1, hL2⟩ := hb
  interval_cases i <;> interval_cases l <;> omega

/-- The free classes of the native points: a native point lies in a free class exactly when it, `w - V` or `w - U` is an H or V
site (`w - V = (w.1 + 2, w.2 - 2a)`, `w - U = (w.1 - (a+1), w.2 - (a-1))`). -/
theorem freeClass_native_iff {a : ℤ} (ha : 4 ≤ a) {w : Site} (hw : NativeT a w.1 w.2) :
    FreeClass a w ↔ (FreeSite a w.1 w.2 ∨ FreeSite a (w.1 + 2) (w.2 - 2 * a) ∨
      FreeSite a (w.1 - (a + 1)) (w.2 - (a - 1))) := by
  constructor
  · rintro ⟨u, ⟨i, l, hl⟩, hu⟩
    rcases native_free_alias ha hw hu hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      have hu' : u = w := by
        rw [hl]
        ext <;> simp
      rw [hu'] at hu
      exact hu
    · right
      left
      have hu' : u = (w.1 + 2, w.2 - 2 * a) := by
        rw [hl]
        ext <;> simp
      rw [hu'] at hu
      exact hu
    · right
      right
      have hu' : u = (w.1 - (a + 1), w.2 - (a - 1)) := by
        rw [hl]
        ext <;> simp
      rw [hu'] at hu
      exact hu
  · rintro (h | h | h)
    · exact ⟨w, ⟨0, 0, by ext <;> simp⟩, h⟩
    · exact ⟨(w.1 + 2, w.2 - 2 * a), ⟨0, 1, by ext <;> simp⟩, h⟩
    · exact ⟨(w.1 - (a + 1), w.2 - (a - 1)), ⟨1, 0, by ext <;> simp⟩, h⟩

/-- The corners of the unit square with lower-left corner `u`. -/
def SqCorner (u v : Site) : Prop :=
  v = u ∨ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) ∨ v = (u.1 + 1, u.2 + 1)

/-- A site outside the unit square with lower-left corner `u`. -/
def SqOut (u i : Site) : Prop :=
  i ≠ u ∧ i ≠ (u.1 + 1, u.2) ∧ i ≠ (u.1, u.2 + 1) ∧ i ≠ (u.1 + 1, u.2 + 1)

/-- The square clause of the unit square with lower-left corner `u` (the negation of "every corner keeps an input inside"):
some corner `v` is white and retains an input outside the square. -/
def SqClause (a η : ℤ) (F : Field) (u : Site) : Prop :=
  ∃ v, SqCorner u v ∧ laplacian F v = 0 ∧ ∃ i, TwosSel a η F v i ∧ SqOut u i

theorem aliasOf_refl (a : ℤ) (c : Site) : AliasOf a c c := ⟨0, 0, by ext <;> simp⟩

theorem aliasOf_trans {a : ℤ} {c u z : Site} (h1 : AliasOf a c u) (h2 : AliasOf a u z) : AliasOf a c z := by
  obtain ⟨i1, l1, rfl⟩ := h1
  obtain ⟨i2, l2, rfl⟩ := h2
  exact ⟨i1 + i2, l1 + l2, by ext <;> simp <;> ring⟩

theorem aliasOf_symm {a : ℤ} {c u : Site} (h : AliasOf a c u) : AliasOf a u c := by
  obtain ⟨i, l, rfl⟩ := h
  exact ⟨-i, -l, by ext <;> simp <;> ring⟩

/-- The free classes are invariant under the lattice. -/
theorem freeClass_alias {a : ℤ} {c c' : Site} (h : AliasOf a c c') : FreeClass a c ↔ FreeClass a c' := by
  constructor
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, aliasOf_trans (aliasOf_symm h) hu, hf⟩
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, aliasOf_trans h hu, hf⟩

/-- A native copy of a non-free point is non-free as soon as the native local test fails. -/
theorem nonfree_of_native_test {a : ℤ} (ha : 4 ≤ a) {v w : Site} (hw : AliasOf a v w) (hwn : NativeT a w.1 w.2)
    (ht : ¬ (FreeSite a w.1 w.2 ∨ FreeSite a (w.1 + 2) (w.2 - 2 * a) ∨ FreeSite a (w.1 - (a + 1)) (w.2 - (a - 1)))) :
    ¬ FreeClass a v := by
  intro h
  exact ht ((freeClass_native_iff ha hwn).mp ((freeClass_alias hw).mp h))

/-- The Laplacian vanishes at a white point of the charge table (the native copy of the corner). -/
theorem lap_zero_of_charge {k : ℕ} {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {v w : Site} (hw : AliasOf (2 * (k : ℤ) + 4) v w) (hwn : NativeT (2 * (k : ℤ) + 4) w.1 w.2)
    (hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) w) ∧
        ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) w)) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) w) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) w))) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) v = 0 := by
  rw [← laplacian_twos_alias hagree hperiod hw, laplacian_twos_native k hagree hperiod hwn]
  rcases hcharge with ⟨he, hb⟩ | ⟨hn, hb⟩
  · rw [if_pos he, if_neg hb]
  · rw [if_neg hn, if_pos hb]

/-- The generic witness: a white corner `v` of the square whose native copy `w` is a non-free candidate point, with its
candidate input outside the square, gives the square clause for every sign. -/
theorem sq_of_witness {a η : ℤ} {F : Field} {u v w : Site} (hv : SqCorner u v) (hlap : laplacian F v = 0)
    (hnf : ¬ FreeClass a v) (hw : AliasOf a v w) (hwn : NativeT a w.1 w.2) (hg : CandGuard a w.1 w.2)
    (hout : SqOut u (v.1 + (candDisp a w.1 w.2).1, v.2 + (candDisp a w.1 w.2).2)) : SqClause a η F u :=
  ⟨v, hv, hlap, _, (twosSel_white_nonfree_iff hlap hnf).mpr ⟨w, hw, hwn, hg, rfl⟩, hout⟩

/-- The candidate direction on the east diagonal. -/
theorem candDisp_E {a p q : ℤ} (hE : CandE a p q) : candDisp a p q = (1, 0) := by
  have hnL : ¬ (CandLow a p q ∨ CandHigh a p q) := by
    simp only [CandE, CandLow, CandHigh] at hE ⊢
    omega
  unfold candDisp
  rw [if_pos hE, if_neg hnL]

/-- The candidate direction on the west diagonal. -/
theorem candDisp_W {a p q : ℤ} (hW : CandW a p q) : candDisp a p q = (-1, 0) := by
  have hnE : ¬ CandE a p q := by
    simp only [CandE, CandW] at hW ⊢
    omega
  have hnL : ¬ (CandLow a p q ∨ CandHigh a p q) := by
    simp only [CandW, CandLow, CandHigh] at hW ⊢
    omega
  unfold candDisp
  rw [if_neg hnE, if_pos hW, if_neg hnL]

/-- The candidate direction on the low band, below its middle row: down. -/
theorem candDisp_low_down {a p q : ℤ} (hL : CandLow a p q) (hm : q < a - 1) : candDisp a p q = (0, -1) := by
  have hnE : ¬ CandE a p q := by
    simp only [CandE, CandLow] at hL ⊢
    omega
  have hnW : ¬ CandW a p q := by
    simp only [CandW, CandLow] at hL ⊢
    omega
  unfold candDisp
  rw [if_neg hnE, if_neg hnW, if_pos (Or.inl hL), if_pos hL, if_pos hm]

/-- The candidate direction on the low band, above its middle row: up. -/
theorem candDisp_low_up {a p q : ℤ} (hL : CandLow a p q) (hm : ¬ q < a - 1) : candDisp a p q = (0, 1) := by
  have hnE : ¬ CandE a p q := by
    simp only [CandE, CandLow] at hL ⊢
    omega
  have hnW : ¬ CandW a p q := by
    simp only [CandW, CandLow] at hL ⊢
    omega
  unfold candDisp
  rw [if_neg hnE, if_neg hnW, if_pos (Or.inl hL), if_pos hL, if_neg hm]

/-- The candidate direction on the high band, below its middle row: down. -/
theorem candDisp_high_down {a p q : ℤ} (hH : CandHigh a p q) (hm : q < 2 * a - 1) : candDisp a p q = (0, -1) := by
  have hnE : ¬ CandE a p q := by
    simp only [CandE, CandHigh] at hH ⊢
    omega
  have hnW : ¬ CandW a p q := by
    simp only [CandW, CandHigh] at hH ⊢
    omega
  have hnL : ¬ CandLow a p q := by
    simp only [CandLow, CandHigh] at hH ⊢
    omega
  unfold candDisp
  rw [if_neg hnE, if_neg hnW, if_pos (Or.inr hH), if_neg hnL, if_pos hm]

/-- The candidate direction on the high band, above its middle row: up. -/
theorem candDisp_high_up {a p q : ℤ} (hH : CandHigh a p q) (hm : ¬ q < 2 * a - 1) : candDisp a p q = (0, 1) := by
  have hnE : ¬ CandE a p q := by
    simp only [CandE, CandHigh] at hH ⊢
    omega
  have hnW : ¬ CandW a p q := by
    simp only [CandW, CandHigh] at hH ⊢
    omega
  have hnL : ¬ CandLow a p q := by
    simp only [CandLow, CandHigh] at hH ⊢
    omega
  unfold candDisp
  rw [if_neg hnE, if_neg hnW, if_pos (Or.inr hH), if_neg hnL, if_neg hm]

/-- The free table on the H site `(1,0)`. -/
theorem freeDisp_H0 {a η x y : ℤ} (hH0 : x = 1 ∧ y = 0) : freeDisp a η x y = (0, -η) := by
  unfold freeDisp
  rw [if_pos (show FreeHSite a x y from Or.inl hH0), if_pos hH0]

/-- The free table on an even H site other than `(1,0)`. -/
theorem freeDisp_Heven {a η x y : ℤ} (hH : FreeHSite a x y) (hn : ¬ (x = 1 ∧ y = 0)) (he : EvenSite (x, y)) :
    freeDisp a η x y = (1, 0) := by
  unfold freeDisp
  rw [if_pos hH, if_neg hn, if_pos he]

/-- The free table on an odd H site. -/
theorem freeDisp_Hodd {a η x y : ℤ} (hH : FreeHSite a x y) (hn : ¬ (x = 1 ∧ y = 0)) (ho : ¬ EvenSite (x, y)) :
    freeDisp a η x y = (0, 1) := by
  unfold freeDisp
  rw [if_pos hH, if_neg hn, if_neg ho]

/-- The free table on `V_0 = (0,0)`. -/
theorem freeDisp_V0 {a η x y : ℤ} (hV0 : x = 0 ∧ y = 0) : freeDisp a η x y = (1, 0) := by
  have hnH : ¬ FreeHSite a x y := by
    simp only [FreeHSite]
    omega
  unfold freeDisp
  rw [if_neg hnH, if_pos hV0]

/-- The free table on an even V site other than `(0,0)`. -/
theorem freeDisp_Veven {a η x y : ℤ} (hV : FreeVSite a x y) (hn : ¬ (x = 0 ∧ y = 0)) (he : EvenSite (x, y)) :
    freeDisp a η x y = (η, 0) := by
  have hnH : ¬ FreeHSite a x y := by
    simp only [FreeVSite, FreeHSite] at hV ⊢
    omega
  unfold freeDisp
  rw [if_neg hnH, if_neg hn, if_pos he]

/-- The free table on an odd V site. -/
theorem freeDisp_Vodd {a η x y : ℤ} (hV : FreeVSite a x y) (hn : ¬ (x = 0 ∧ y = 0)) (ho : ¬ EvenSite (x, y)) :
    freeDisp a η x y = (0, -η) := by
  have hnH : ¬ FreeHSite a x y := by
    simp only [FreeVSite, FreeHSite] at hV ⊢
    omega
  unfold freeDisp
  rw [if_neg hnH, if_neg hn, if_neg ho]

/-- The generic free witness: a white corner `v` of the square, with a free alias `h` (an H or V site), whose retained input
`v + freeDisp h` leaves the square, gives the square clause for the sign `η`. -/
theorem sq_of_free_witness {a η : ℤ} {F : Field} {u v h : Site} (hv : SqCorner u v) (hlap : laplacian F v = 0)
    (hh : AliasOf a v h) (hfs : FreeSite a h.1 h.2)
    (hout : SqOut u (v.1 + (freeDisp a η h.1 h.2).1, v.2 + (freeDisp a η h.1 h.2).2)) : SqClause a η F u :=
  ⟨v, hv, hlap, _, (twosSel_white_freeClass hlap ⟨h, hh, hfs⟩).mpr ⟨h, hh, hfs, rfl⟩, hout⟩

/-- The free witness with explicit coordinates of the free alias and an explicit displacement `d` of the free table. -/
theorem sq_of_free_witness' {a η : ℤ} {F : Field} {u v : Site} {h1 h2 : ℤ} {d : Site} (hv : SqCorner u v)
    (hlap : laplacian F v = 0) (hh : AliasOf a v (h1, h2)) (hfs : FreeSite a h1 h2) (hdisp : freeDisp a η h1 h2 = d)
    (hout : SqOut u (v.1 + d.1, v.2 + d.2)) : SqClause a η F u := by
  refine ⟨v, hv, hlap, (v.1 + d.1, v.2 + d.2), ?_, hout⟩
  refine (twosSel_white_freeClass hlap ⟨(h1, h2), hh, hfs⟩).mpr ⟨(h1, h2), hh, hfs, ?_⟩
  show (v.1 + d.1, v.2 + d.2) = (v.1 + (freeDisp a η h1 h2).1, v.2 + (freeDisp a η h1 h2).2)
  rw [hdisp]

end FLatticePaper.TwosEPolicy
