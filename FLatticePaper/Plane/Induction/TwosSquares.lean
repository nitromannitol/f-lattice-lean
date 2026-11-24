import FLatticePaper.Plane.Induction.TwosQuota

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

end FLatticePaper.TwosEPolicy
