import FLattice.Auxiliary.PlusEvenPhysicalCells
import FLattice.Auxiliary.PlusEvenRepresentative
import FLattice.Auxiliary.PlusEvenSpecialValues

/-!
# Physical incoming deficits in the two low rows

These are evaluations of the literal corrected global even-plus profile.
The predecessor values include the wrapped left edge, the diagonal-period
corrections, and both exceptional representative heights. No superharmonicity
claim outside the stated rows is made here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

private theorem row_zero (m : Parameter) (s : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    profile m (2 * s + (v.val : ℤ)) (e.val : ℤ) =
      representativeHeight e v 0 s := by
  have hm := m.property
  simpa only [mul_zero, zero_add] using
    profile_at_cell m 0 s e v (by omega) (by omega) hs hsm (by omega)

private theorem row_one (m : Parameter) (s : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    profile m (2 * m.val + 2 * s + (v.val : ℤ)) (e.val : ℤ) =
      representativeHeight e v 1 s := by
  have hm := m.property
  simpa only [mul_one] using
    profile_at_cell m 1 s e v (by omega) (by omega) hs hsm (by omega)

private theorem row_two (m : Parameter) (s : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    profile m (4 * m.val + 2 * s + (v.val : ℤ)) (e.val : ℤ) =
      representativeHeight e v 2 s := by
  have hm := m.property
  have h := profile_at_cell m 2 s e v (by omega) (by omega) hs hsm (by omega)
  rw [show 2 * m.val * 2 = 4 * m.val by ring] at h
  exact h

private theorem below_row_zero (m : Parameter) (x : ℤ) :
    profile m x (-1) = profile m (x + 2 * m.val) 1 + 1 := by
  have h := profile_add_diagonal_period m x (-1)
  norm_num only at h
  omega

private theorem above_row_one (m : Parameter) (x : ℤ) :
    profile m (x + 2 * m.val) 2 = profile m x 0 - 2 := by
  have h := profile_add_diagonal_period m x 0
  norm_num only at h
  omega

/-- The physical `00` deficit in representative row zero. -/
theorem incomingDeficit_00_row_zero (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * s) 0 = 0 := by
  have hcenter := row_zero m s 0 0 hs hsm
  have hright := row_zero m s 0 1 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_00_row_zero s hs, height_01_row_zero s hs] at hcenter hright
  have hleft : profile m (2 * s - 1) 0 = -1 := by
    by_cases hz : s = 0
    · simpa only [hz, mul_zero, zero_sub] using profile_left_of_origin m
    · have h := row_zero m (s - 1) 0 1 (by omega) (by omega)
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        height_01_row_zero (s - 1) (by omega)] at h
      rw [show 2 * (s - 1) + 1 = 2 * s - 1 by ring] at h
      exact h
  have hstar := incomingDeficit_00 m 0 s
  simp only [mul_zero, zero_add] at hstar
  rw [hstar, hcenter, hleft, hright]
  omega

/-- The physical `01` deficit in representative row zero. -/
theorem incomingDeficit_01_row_zero (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * s + 1) 0 = if 1 ≤ s then 1 else 0 := by
  have hcenter := row_zero m s 0 1 hs hsm
  have hup := row_zero m s 1 1 hs hsm
  have hnext := row_one m s 1 1 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    height_01_row_zero s hs, height_11_row_zero s hs,
    height_11_row_one s hs] at hcenter hup hnext
  have hdown := below_row_zero m (2 * s + 1)
  rw [show 2 * s + 1 + 2 * m.val = 2 * m.val + 2 * s + 1 by ring,
    hnext] at hdown
  have hstar := incomingDeficit_01 m 0 s
  simp only [mul_zero, zero_add] at hstar
  rw [hstar, hcenter, hdown, hup]
  omega

/-- The prescribed `10` site has deficit four; the rest of row zero has deficit zero. -/
theorem incomingDeficit_10_row_zero (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * s) 1 = if s = 0 then 4 else 0 := by
  have hcenter := row_zero m s 1 0 hs hsm
  have hdown := row_zero m s 0 0 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_10_row_zero s hs, height_00_row_zero s hs] at hcenter hdown
  have hstar := incomingDeficit_10 m 0 s
  simp only [mul_zero, zero_add] at hstar
  rw [hstar, hcenter, hdown, profile_even_segment m s hs hsm]
  omega

/-- The physical `11` deficit in representative row zero, including its override. -/
theorem incomingDeficit_11_row_zero (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * s + 1) 1 = 0 := by
  have hm := m.property
  have hcenter := row_zero m s 1 1 hs hsm
  have hleft := row_zero m s 1 0 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_11_row_zero s hs, height_10_row_zero s hs] at hcenter hleft
  have hright : profile m (2 * s + 2) 1 = -2 := by
    by_cases hnext : s + 1 < m.val
    · have h := row_zero m (s + 1) 1 0 (by omega) hnext
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        add_zero, height_10_row_zero (s + 1) (by omega), if_neg (by omega : s + 1 ≠ 0)] at h
      rw [show 2 * (s + 1) = 2 * s + 2 by ring] at h
      exact h
    · have h := row_one m 0 1 0 (by omega) (by omega)
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        mul_zero, add_zero, height_10_row_one 0 (by omega)] at h
      rw [show 2 * s + 2 = 2 * m.val by omega]
      exact h
  have hstar := incomingDeficit_11 m 0 s
  simp only [mul_zero, zero_add] at hstar
  rw [hstar, hcenter, hleft, hright]
  omega

/-- The physical `00` deficit in representative row one. -/
theorem incomingDeficit_00_row_one (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * m.val + 2 * s) 0 = if s = 0 then 1 else 0 := by
  have hm := m.property
  have hcenter := row_one m s 0 0 hs hsm
  have hright := row_one m s 0 1 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_00_row_one s hs, height_01_row_one s hs] at hcenter hright
  have hleft : profile m (2 * m.val + 2 * s - 1) 0 =
      if s = 0 then -1 else -2 := by
    by_cases hz : s = 0
    · have h := row_zero m (m.val - 1) 0 1 (by omega) (by omega)
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        height_01_row_zero (m.val - 1) (by omega)] at h
      rw [if_pos hz]
      rw [show 2 * m.val + 2 * s - 1 = 2 * (m.val - 1) + 1 by omega]
      exact h
    · have h := row_one m (s - 1) 0 1 (by omega) (by omega)
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        height_01_row_one (s - 1) (by omega)] at h
      rw [if_neg hz]
      rw [show 2 * m.val + 2 * (s - 1) + 1 = 2 * m.val + 2 * s - 1 by ring] at h
      exact h
  have hstar := incomingDeficit_00 m 1 s
  simp only [mul_one] at hstar
  rw [hstar, hcenter, hleft, hright]
  omega

/-- The physical `01` deficit in representative row one. -/
theorem incomingDeficit_01_row_one (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * m.val + 2 * s + 1) 0 = if 1 ≤ s then 1 else 0 := by
  have hcenter := row_one m s 0 1 hs hsm
  have hup := row_one m s 1 1 hs hsm
  have hnext := row_two m s 1 1 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    height_01_row_one s hs, height_11_row_one s hs] at hcenter hup hnext
  have hheight : representativeHeight 1 1 2 s = if s = 0 then -3 else -4 := by
    rw [height_11_eq, if_neg (by omega)]
    unfold PlusEvenBulk.u11 PlusEvenBulk.h11
    omega
  rw [hheight] at hnext
  have hdown := below_row_zero m (2 * m.val + 2 * s + 1)
  rw [show 2 * m.val + 2 * s + 1 + 2 * m.val = 4 * m.val + 2 * s + 1 by ring,
    hnext] at hdown
  have hstar := incomingDeficit_01 m 1 s
  simp only [mul_one] at hstar
  rw [hstar, hcenter, hdown, hup]
  omega

/-- The physical `10` deficit in representative row one. -/
theorem incomingDeficit_10_row_one (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * m.val + 2 * s) 1 = if 1 ≤ s then 1 else 0 := by
  have hcenter := row_one m s 1 0 hs hsm
  have hdown := row_one m s 0 0 hs hsm
  have hprevious := row_zero m s 0 0 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_10_row_one s hs, height_00_row_one s hs,
    height_00_row_zero s hs] at hcenter hdown hprevious
  have hup := above_row_one m (2 * s)
  rw [show 2 * s + 2 * m.val = 2 * m.val + 2 * s by ring, hprevious] at hup
  have hstar := incomingDeficit_10 m 1 s
  simp only [mul_one] at hstar
  rw [hstar, hcenter, hdown, hup]
  omega

/-- The physical `11` deficit in representative row one, including the right wrap. -/
theorem incomingDeficit_11_row_one (m : Parameter) (s : ℤ)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    incomingDeficit m (2 * m.val + 2 * s + 1) 1 = 0 := by
  have hm := m.property
  have hcenter := row_one m s 1 1 hs hsm
  have hleft := row_one m s 1 0 hs hsm
  simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, height_11_row_one s hs, height_10_row_one s hs] at hcenter hleft
  have hright : profile m (2 * m.val + 2 * s + 2) 1 = -2 := by
    by_cases hnext : s + 1 < m.val
    · have h := row_one m (s + 1) 1 0 (by omega) hnext
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        add_zero, height_10_row_one (s + 1) (by omega)] at h
      rw [show 2 * m.val + 2 * (s + 1) = 2 * m.val + 2 * s + 2 by ring] at h
      exact h
    · have h := row_two m 0 1 0 (by omega) (by omega)
      have hheight : representativeHeight 1 0 2 0 = -2 := by decide
      simp only [Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
        mul_zero, add_zero, hheight] at h
      rw [show 2 * m.val + 2 * s + 2 = 4 * m.val by omega]
      exact h
  have hstar := incomingDeficit_11 m 1 s
  simp only [mul_one] at hstar
  rw [hstar, hcenter, hleft, hright]
  omega

end FLattice.Auxiliary.PlusEvenProfile
