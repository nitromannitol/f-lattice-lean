import FLatticePaper.Farey.Recursion

namespace FLatticePaper.Farey

abbrev Birth := Word × Parity

/-- The fraction, in reduced coordinates, at the given birth register. -/
def Birth.fraction (birth : Birth) : Fraction := (parentsAt birth.1).current birth.2

theorem Birth.interior (birth : Birth) : birth.fraction.Interior :=
  (parentsAt_valid birth.1).current_interior birth.2

theorem Birth.reduced (birth : Birth) : birth.fraction.Reduced :=
  (parentsAt_valid birth.1).current_reduced birth.2

private def liftCoeffs (digit : Digit) (coeffs : ℤ × ℤ) : ℤ × ℤ :=
  match digit with
  | .one => (coeffs.1 + 2 * coeffs.2, coeffs.1 + coeffs.2)
  | .two => (coeffs.1, coeffs.1 + coeffs.2)
  | .three => (coeffs.1 + 2 * coeffs.2, coeffs.2)

private theorem liftCoeffs_injective (digit : Digit) : Function.Injective (liftCoeffs digit) := by
  intro first second heq
  have hodd := congrArg Prod.fst heq
  have heven := congrArg Prod.snd heq
  cases digit <;> apply Prod.ext <;> dsimp [liftCoeffs] at hodd heven ⊢ <;> omega

private theorem combine_liftCoeffs (parents : Parents) (digit : Digit) (coeffs : ℤ × ℤ) :
    parents.combine (liftCoeffs digit coeffs).1 (liftCoeffs digit coeffs).2 =
      (parents.step digit).combine coeffs.1 coeffs.2 := by
  cases digit <;> apply Fraction.ext <;>
    dsimp [liftCoeffs, Parents.step, Parents.current, Parents.combine] <;> ring

private def coeffsAt : Word → Parity → ℤ × ℤ
  | [], .odd => (1, 1)
  | [], .even => (2, 1)
  | digit :: tail, parity => liftCoeffs digit (coeffsAt tail parity)

private theorem coeffsAt_pos (word : Word) (parity : Parity) :
    0 < (coeffsAt word parity).1 ∧ 0 < (coeffsAt word parity).2 := by
  induction word with
  | nil => cases parity <;> exact ⟨by decide, by decide⟩
  | cons digit tail ih =>
    obtain ⟨hodd, heven⟩ := ih
    cases digit <;> dsimp [coeffsAt, liftCoeffs] <;> omega

private theorem walk_current_eq_combine (parents : Parents) (word : Word) (parity : Parity) :
    (parents.walk word).current parity =
      parents.combine (coeffsAt word parity).1 (coeffsAt word parity).2 := by
  induction word generalizing parents with
  | nil => cases parity <;> rfl
  | cons digit tail ih =>
    rw [Parents.walk_cons, ih]
    exact (combine_liftCoeffs parents digit (coeffsAt tail parity)).symm

private theorem birth_fraction_eq (birth : Birth) :
    birth.fraction = ⟨(coeffsAt birth.1 birth.2).2,
      (coeffsAt birth.1 birth.2).1 + (coeffsAt birth.1 birth.2).2⟩ := by
  unfold Birth.fraction parentsAt
  rw [walk_current_eq_combine]
  simp [root, Parents.combine]

private def sector (coeffs : ℤ × ℤ) : Parity ⊕ Digit :=
  if coeffs.1 = coeffs.2 then .inl .odd
  else if coeffs.1 = 2 * coeffs.2 then .inl .even
  else if coeffs.1 < coeffs.2 then .inr .two
  else if coeffs.1 < 2 * coeffs.2 then .inr .one
  else .inr .three

private theorem sector_liftCoeffs (digit : Digit) (coeffs : ℤ × ℤ)
    (hodd : 0 < coeffs.1) (heven : 0 < coeffs.2) :
    sector (liftCoeffs digit coeffs) = .inr digit := by
  cases digit <;> dsimp [sector, liftCoeffs] <;>
    (repeat' first | rfl | omega | split)

private theorem sector_coeffsAt (word : Word) (parity : Parity) :
    sector (coeffsAt word parity) =
      match word with
      | [] => .inl parity
      | digit :: _ => .inr digit := by
  cases word with
  | nil => cases parity <;> rfl
  | cons digit tail =>
    exact sector_liftCoeffs digit _ (coeffsAt_pos tail parity).1 (coeffsAt_pos tail parity).2

private theorem eq_of_coeffsAt_eq (word other : Word) (parity otherParity : Parity)
    (heq : coeffsAt word parity = coeffsAt other otherParity) :
    (word, parity) = (other, otherParity) := by
  induction word generalizing other parity otherParity with
  | nil =>
    have hsector := congrArg sector heq
    rw [sector_coeffsAt, sector_coeffsAt] at hsector
    cases other with
    | nil => exact congrArg (fun slot => ([], slot)) (Sum.inl.inj hsector)
    | cons digit tail => cases hsector
  | cons digit tail ih =>
    have hsector := congrArg sector heq
    rw [sector_coeffsAt, sector_coeffsAt] at hsector
    cases other with
    | nil => cases hsector
    | cons otherDigit otherTail =>
      have hdigit : digit = otherDigit := Sum.inr.inj hsector
      subst otherDigit
      have htail := liftCoeffs_injective digit heq
      have heqTail := ih otherTail parity otherParity htail
      exact congrArg (fun (birth : Birth) => (digit :: birth.1, birth.2)) heqTail

theorem Birth.fraction_injective : Function.Injective Birth.fraction := by
  rintro ⟨word, parity⟩ ⟨other, otherParity⟩ heq
  rw [birth_fraction_eq, birth_fraction_eq] at heq
  have hnum := congrArg Fraction.num heq
  have hden := congrArg Fraction.den heq
  dsimp at hnum hden
  apply eq_of_coeffsAt_eq
  apply Prod.ext
  · omega
  · exact hnum

private theorem eq_one_of_coprime_diagonal {oddCoeff evenCoeff : ℤ} (heven : 0 < evenCoeff)
    (hc : IsCoprime oddCoeff evenCoeff) (factor : ℤ) (heq : oddCoeff = factor * evenCoeff) :
    evenCoeff = 1 := by
  obtain ⟨aCoeff, bCoeff, hbezout⟩ := hc
  have hdvd : evenCoeff ∣ (1 : ℤ) := by
    refine ⟨aCoeff * factor + bCoeff, ?_⟩
    rw [← hbezout, heq]
    ring
  exact Int.eq_one_of_dvd_one heven.le hdvd

private theorem coprime_two {oddCoeff evenCoeff : ℤ} (hc : IsCoprime oddCoeff evenCoeff) :
    IsCoprime oddCoeff (evenCoeff - oddCoeff) := by
  obtain ⟨aCoeff, bCoeff, hbezout⟩ := hc
  exact ⟨aCoeff + bCoeff, bCoeff, by rw [← hbezout]; ring⟩

private theorem coprime_one {oddCoeff evenCoeff : ℤ} (hc : IsCoprime oddCoeff evenCoeff) :
    IsCoprime (2 * evenCoeff - oddCoeff) (oddCoeff - evenCoeff) := by
  obtain ⟨aCoeff, bCoeff, hbezout⟩ := hc
  exact ⟨aCoeff + bCoeff, 2 * aCoeff + bCoeff, by rw [← hbezout]; ring⟩

private theorem coprime_three {oddCoeff evenCoeff : ℤ} (hc : IsCoprime oddCoeff evenCoeff) :
    IsCoprime (oddCoeff - 2 * evenCoeff) evenCoeff := by
  obtain ⟨aCoeff, bCoeff, hbezout⟩ := hc
  exact ⟨aCoeff, 2 * aCoeff + bCoeff, by rw [← hbezout]; ring⟩

private def prepend (digit : Digit) {coeffs : ℤ × ℤ}
    (birth : {birth : Birth // coeffsAt birth.1 birth.2 = coeffs}) :
    {birth : Birth // coeffsAt birth.1 birth.2 = liftCoeffs digit coeffs} :=
  ⟨(digit :: birth.val.1, birth.val.2), congrArg (liftCoeffs digit) birth.property⟩

private def locateCoeffs (oddCoeff evenCoeff : ℤ) (hodd : 0 < oddCoeff) (heven : 0 < evenCoeff)
    (hc : IsCoprime oddCoeff evenCoeff) :
    {birth : Birth // coeffsAt birth.1 birth.2 = (oddCoeff, evenCoeff)} :=
  if h : oddCoeff = evenCoeff then
    ⟨([], .odd), by
      have hone := eq_one_of_coprime_diagonal heven hc 1 (by omega)
      change (1, 1) = (oddCoeff, evenCoeff)
      simp [h, hone]⟩
  else if h : oddCoeff = 2 * evenCoeff then
    ⟨([], .even), by
      have hone := eq_one_of_coprime_diagonal heven hc 2 h
      change (2, 1) = (oddCoeff, evenCoeff)
      simp [h, hone]⟩
  else if h : oddCoeff < evenCoeff then
    let lifted := prepend .two
      (locateCoeffs oddCoeff (evenCoeff - oddCoeff) hodd (by omega) (coprime_two hc))
    ⟨lifted.val, lifted.property.trans (Prod.ext rfl (by dsimp [liftCoeffs]; omega))⟩
  else if h : oddCoeff < 2 * evenCoeff then
    let lifted := prepend .one
      (locateCoeffs (2 * evenCoeff - oddCoeff) (oddCoeff - evenCoeff)
        (by omega) (by omega) (coprime_one hc))
    ⟨lifted.val, lifted.property.trans (by apply Prod.ext <;> dsimp [liftCoeffs] <;> omega)⟩
  else
    let lifted := prepend .three
      (locateCoeffs (oddCoeff - 2 * evenCoeff) evenCoeff (by omega) heven (coprime_three hc))
    ⟨lifted.val, lifted.property.trans (Prod.ext (by dsimp [liftCoeffs]; omega) rfl)⟩
termination_by (oddCoeff + evenCoeff).toNat
decreasing_by all_goals omega

private def locateFraction (fraction : Fraction) (hinterior : fraction.Interior)
    (hreduced : fraction.Reduced) :
    {birth : Birth // coeffsAt birth.1 birth.2 = (fraction.den - fraction.num, fraction.num)} :=
  locateCoeffs (fraction.den - fraction.num) fraction.num (by have := hinterior.2; omega)
    hinterior.1 (by
      obtain ⟨aCoeff, bCoeff, hbezout⟩ := hreduced
      exact ⟨bCoeff, aCoeff + bCoeff, by rw [← hbezout]; ring⟩)

/-- Inverse creation history. Descent has no denominator cutoff: the sum of
the two positive coefficients drops at every step. -/
def birthOf (fraction : Fraction) (hinterior : fraction.Interior) (hreduced : fraction.Reduced) :
    Birth := (locateFraction fraction hinterior hreduced).val

theorem fraction_birthOf (fraction : Fraction) (hinterior : fraction.Interior)
    (hreduced : fraction.Reduced) : (birthOf fraction hinterior hreduced).fraction = fraction := by
  rw [birth_fraction_eq]
  have hcoeff := (locateFraction fraction hinterior hreduced).property
  change coeffsAt (birthOf fraction hinterior hreduced).1
    (birthOf fraction hinterior hreduced).2 = _ at hcoeff
  rw [hcoeff]
  exact Fraction.ext rfl (by dsimp; omega)

theorem existsUnique_birth (fraction : Fraction) (hinterior : fraction.Interior)
    (hreduced : fraction.Reduced) : ∃! birth : Birth, birth.fraction = fraction :=
  ⟨birthOf fraction hinterior hreduced, fraction_birthOf fraction hinterior hreduced,
    fun _ heq => Birth.fraction_injective (heq.trans (fraction_birthOf ..).symm)⟩

theorem Birth.birthOf_fraction (birth : Birth) (hinterior : birth.fraction.Interior)
    (hreduced : birth.fraction.Reduced) : birthOf birth.fraction hinterior hreduced = birth :=
  Birth.fraction_injective (fraction_birthOf birth.fraction hinterior hreduced)

end FLatticePaper.Farey
