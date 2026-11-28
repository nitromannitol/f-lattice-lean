import Mathlib

/-! # Separation margins of the even alternate child along its second period (arithmetic) -/

namespace FLatticePaper.Tiles.AltLatticeEvenVArith

theorem m_e_Pm (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + 3*d1*d2 + 4*d1*n1 + 3*d1*n2 - 6*d1 + d2^2 + 3*d2*n1 + 2*d2*n2 - 3*d2 - 2*n1^2 - 3*n1*n2 + 2*n1 - n2^2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_e_Qp2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 + d1*n2 - 6*d1 + d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_e_Qm1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 + d1*n2 - 6*d1 + d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_e_Qm2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 4*d1^2 + 2*d1*d2 + 8*d1*n1 - 6*d1 + 4*d2*n1 - 3*d2 - 4*n1^2 - 2*n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_e_H1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (t2 : d2 < 2 * d1) (t4 : n2 ≤ 2 * n1) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 - d1*n2 - 6*d1 + 3*d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_e_H2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (t1 : d2 < d1) :
    0 < 2*d1*d2 + 4*d1*n2 - 6*d1 + d2^2 + 2*d2*n2 - 3*d2 - 2*n1*n2 + 2*n1 - n2^2 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_Pm (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + 3*d1*d2 + 4*d1*n1 + 5*d1*n2 - 6*d1 + d2^2 + d2*n1 + 2*d2*n2 - 3*d2 - 2*n1^2 - 3*n1*n2 + 2*n1 - n2^2 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_Qp2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 - d1*n2 - 6*d1 + 3*d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_Qm1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 - d1*n2 - 6*d1 + 3*d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_Qm2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) :
    0 < 4*d1^2 + 2*d1*d2 + 8*d1*n1 + 2*d1*n2 - 6*d1 + 2*d2*n1 - 3*d2 - 4*n1^2 - 2*n1*n2 + 2*n1 + n2 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_H1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (t2 : d2 < 2 * d1) (t4 : n2 ≤ 2 * n1) :
    0 < 2*d1^2 + d1*d2 + 4*d1*n1 + d1*n2 - 6*d1 + d2*n1 - 3*d2 - 2*n1^2 - n1*n2 + 2*n1 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

theorem m_o_H2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (t1 : d2 < d1) :
    0 < 2*d1*d2 + 4*d1*n2 - 6*d1 + d2^2 + 2*d2*n2 - 3*d2 - 2*n1*n2 + 2*n1 - n2^2 + n2 - 3 := by
  nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3]

end FLatticePaper.Tiles.AltLatticeEvenVArith
