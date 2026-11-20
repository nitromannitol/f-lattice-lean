import FLattice.Auxiliary.PlusOddClock

/-!
# The two odd bulk paths and their branching contacts

These inequalities use the unmodified bulk clock at the virtual incoming
labels. They hold for all signed parameters and indices. The real boundary
overrides and wrapped physical inputs require separate identities.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

/-- The selected 00 edge follows up on the left path and down on the right path. -/
theorem bulkClock_00_selected (m r s : ℤ) :
    (if r - s ≤ 1 then bulkClock m r s 1 0 else bulkClock m (r + 1) s 1 0) <
      bulkClock m r s 0 0 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- Both incoming clocks decrease at a black 00 site. -/
theorem bulkClock_00_of_black (m r s : ℤ) (ha : ¬(1 ≤ r - s ∧ r - s ≤ 3)) :
    bulkClock m (r + 1) s 1 0 < bulkClock m r s 0 0 ∧
      bulkClock m r s 1 0 < bulkClock m r s 0 0 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- The selected 01 edge follows the corresponding horizontal path. -/
theorem bulkClock_01_selected (m r s : ℤ) :
    (if r - s ≤ 1 then bulkClock m r s 0 0 else bulkClock m r (s + 1) 0 0) <
      bulkClock m r s 0 1 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- Both inputs decrease at a black 01 site, including its maximum junction. -/
theorem bulkClock_01_of_black (m r s : ℤ) (ha : r - s = 2 ∨ r - s = 3) :
    bulkClock m r s 0 0 < bulkClock m r s 0 1 ∧
      bulkClock m r (s + 1) 0 0 < bulkClock m r s 0 1 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- The selected 10 edge follows the corresponding horizontal path. -/
theorem bulkClock_10_selected (m r s : ℤ) :
    (if r - s ≤ 1 then bulkClock m r (s - 1) 1 1 else bulkClock m r s 1 1) <
      bulkClock m r s 1 0 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- Both inputs decrease at a black 10 site, including its maximum junction. -/
theorem bulkClock_10_of_black (m r s : ℤ) (ha : r - s = 2 ∨ r - s = 3) :
    bulkClock m r (s - 1) 1 1 < bulkClock m r s 1 0 ∧
      bulkClock m r s 1 1 < bulkClock m r s 1 0 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- The selected 11 edge follows up on the left path and down on the right path. -/
theorem bulkClock_11_selected (m r s : ℤ) :
    (if r - s ≤ 2 then bulkClock m (r - 1) s 0 1 else bulkClock m r s 0 1) <
      bulkClock m r s 1 1 := by
  norm_num [bulkClock]
  split_ifs <;> omega

/-- Both incoming clocks decrease at a black 11 site. -/
theorem bulkClock_11_of_black (m r s : ℤ) (ha : ¬(2 ≤ r - s ∧ r - s ≤ 4)) :
    bulkClock m r s 0 1 < bulkClock m r s 1 1 ∧
      bulkClock m (r - 1) s 0 1 < bulkClock m r s 1 1 := by
  norm_num [bulkClock]
  split_ifs <;> omega

end FLattice.Auxiliary.PlusOddProfile
