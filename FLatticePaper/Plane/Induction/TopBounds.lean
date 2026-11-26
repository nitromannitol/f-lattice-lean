import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.W1OffCollarCases
import FLatticePaper.Plane.Induction.SlipPermitH

/-! # The grade bounds of the top witness (step 2 of the top price; audit section 1, "Inputs on actual collars")

For a strict centre `c` and a top witness `v` (`|v − c|_∞ ≤ 1`, `u = v − V ∈ freeH`, `V` the transverse vector), put `y = c − V`.
Then `t(y) = t(c) + T`, `s(y) = s(c)`, and

* even `y`: `L − 2 < t(y) ≤ 2L − 2`, `2n < s(y) < T`;
* odd `y`: `d < t(y) ≤ n + 2d − 2`, `L − 2 < s(y) < T + 2 − c`.

The lower bounds are the strictness of `c`. The upper ones come from the witness: `t(y) = t(u) − n a + d b` with `(a, b) = v − c`.
The one excluded case is `u = H_{d−1}` with `(a, b) = (−1, 1)`: there `s(y) = T − d + 3n`, which violates the strict bound on `s(c)`. -/

namespace FLatticePaper.TopBounds

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollarCases

theorem transverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
  frame.child_modifiedDeck_transverse

/-- `t(z − V) = t(z) + T`. -/
theorem tGrade_sub_transverse (frame : ChildFrame) (z : Site) :
    frame.tGrade (z - frame.child.modifiedDeck.transverse) = frame.tGrade z + w1T frame.child.num frame.child.den := by
  rw [transverse_eq]
  unfold ChildFrame.tGrade w1T
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- `s(z − V) = s(z)`. -/
theorem sGrade_sub_transverse (frame : ChildFrame) (z : Site) :
    frame.sGrade (z - frame.child.modifiedDeck.transverse) = frame.sGrade z := by
  rw [transverse_eq]
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The top witness bounds.** The even and odd ranges of `y = c − V`. -/
theorem top_bounds (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {c v : Site}
    (hc : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c)
    (hv1 : |v.1 - c.1| ≤ 1) (hv2 : |v.2 - c.2| ≤ 1)
    (hu : v - frame.child.modifiedDeck.transverse ∈ frame.freeH) :
    (EvenSite (c - frame.child.modifiedDeck.transverse) →
        (frame.child.den + frame.child.num - 2 < frame.tGrade (c - frame.child.modifiedDeck.transverse) ∧
          frame.tGrade (c - frame.child.modifiedDeck.transverse) ≤ 2 * (frame.child.den + frame.child.num) - 2) ∧
        (2 * frame.child.num < frame.sGrade (c - frame.child.modifiedDeck.transverse) ∧
          frame.sGrade (c - frame.child.modifiedDeck.transverse) < w1T frame.child.num frame.child.den)) ∧
    (¬ EvenSite (c - frame.child.modifiedDeck.transverse) →
        (frame.child.den < frame.tGrade (c - frame.child.modifiedDeck.transverse) ∧
          frame.tGrade (c - frame.child.modifiedDeck.transverse) ≤ frame.child.num + 2 * frame.child.den - 2) ∧
        (frame.child.den + frame.child.num - 2 < frame.sGrade (c - frame.child.modifiedDeck.transverse) ∧
          frame.sGrade (c - frame.child.modifiedDeck.transverse) <
            w1T frame.child.num frame.child.den + (2 - frame.child.den + frame.child.num))) := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  have hs := (strict_grades _ _ c).1 hc
  have hty := tGrade_sub_transverse frame c
  have hsy := sGrade_sub_transverse frame c
  have htc : w1t frame.child.num frame.child.den c = frame.tGrade c := rfl
  have hsc : w1s frame.child.num frame.child.den c = frame.sGrade c := rfl
  rw [htc, hsc] at hs
  have hpar : EvenSite (c - frame.child.modifiedDeck.transverse) ↔ EvenSite c := by
    unfold EvenSite
    rw [transverse_eq]
    simp only [Prod.fst_sub, Prod.snd_sub]
    constructor <;> intro h <;> omega
  -- the witness `u = v − V`
  have hu2 := hu
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hu2
  obtain ⟨-, -, hsp⟩ := hu2
  have htu2 : frame.tGrade (c - frame.child.modifiedDeck.transverse) =
      frame.tGrade (v - frame.child.modifiedDeck.transverse) - frame.child.num * (v.1 - c.1) +
        frame.child.den * (v.2 - c.2) := by
    unfold ChildFrame.tGrade
    rw [transverse_eq]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hpu : frame.tGrade (v - frame.child.modifiedDeck.transverse) % 2 = (v.1 + v.2) % 2 := by
    rw [FLatticePaper.SlipPermitH.tGrade_parity frame (v - frame.child.modifiedDeck.transverse), transverse_eq]
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  have hA := abs_le.1 hv1
  have hB := abs_le.1 hv2
  have hA3 : v.1 - c.1 = -1 ∨ v.1 - c.1 = 0 ∨ v.1 - c.1 = 1 := by omega
  have hB3 : v.2 - c.2 = -1 ∨ v.2 - c.2 = 0 ∨ v.2 - c.2 = 1 := by omega
  -- the strict bounds of `c`
  have hEv : EvenSite c → (frame.child.den + frame.child.num - 2 < frame.tGrade c + w1T frame.child.num frame.child.den ∧
      2 * frame.child.num < frame.sGrade c ∧ frame.sGrade c < w1T frame.child.num frame.child.den) := by
    intro he
    rcases hs with ⟨-, h1, -, h3, h4⟩ | ⟨ho, -⟩
    · exact ⟨by omega, h3, h4⟩
    · exact absurd he ho
  have hOd : ¬ EvenSite c → (frame.child.den < frame.tGrade c + w1T frame.child.num frame.child.den ∧
      frame.child.den + frame.child.num - 2 < frame.sGrade c ∧
      frame.sGrade c < w1T frame.child.num frame.child.den + (2 - frame.child.den + frame.child.num)) := by
    intro ho
    rcases hs with ⟨he, -⟩ | ⟨-, h1, -, h3, h4⟩
    · exact absurd he ho
    · exact ⟨by omega, h3, h4⟩
  constructor
  · -- even `y`
    intro hye
    have hc' : EvenSite c := hpar.1 hye
    have hc'' : (c.1 + c.2) % 2 = 0 := hc'
    obtain ⟨hl1, hl2, hl3⟩ := hEv hc'
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, by omega⟩⟩
    rcases hsp with ⟨hp0, hp1, hp2⟩ | ⟨hp0, hp1, hp2⟩
    · rcases hA3 with h1 | h1 | h1 <;> rcases hB3 with h2 | h2 | h2 <;> (rw [h1, h2] at htu2; omega)
    · rcases hA3 with h1 | h1 | h1 <;> rcases hB3 with h2 | h2 | h2 <;> (rw [h1, h2] at htu2; omega)
  · -- odd `y`
    intro hyo
    have hc' : ¬ EvenSite c := fun h => hyo (hpar.2 h)
    have hcodd : (c.1 + c.2) % 2 = 1 := by
      unfold EvenSite at hc'
      omega
    obtain ⟨hl1, hl2, hl3⟩ := hOd hc'
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, by omega⟩⟩
    rcases hsp with ⟨hp0, hp1, hp2⟩ | ⟨hp0, hp1, hp2⟩
    · -- `u` even: the shift `(a, b)` has odd sum, so `−n a + d b ≤ d`
      rcases hA3 with h1 | h1 | h1 <;> rcases hB3 with h2 | h2 | h2 <;> (rw [h1, h2] at htu2; omega)
    · by_cases hL : v - frame.child.modifiedDeck.transverse = frame.hLast
      · -- `u = H_{d−1}`: the case `(a, b) = (−1, 1)` is excluded by the strict upper bound of `s`
        have hu1 : (v - frame.child.modifiedDeck.transverse).1 = frame.child.den := by
          rw [hL]; rfl
        have hu2' : (v - frame.child.modifiedDeck.transverse).2 = frame.child.num - 1 := by
          rw [hL]; rfl
        have htuL : frame.tGrade (v - frame.child.modifiedDeck.transverse) = frame.child.den := by
          unfold ChildFrame.tGrade
          rw [hu1, hu2']
          ring
        have hsuL : frame.sGrade (v - frame.child.modifiedDeck.transverse) =
            w1T frame.child.num frame.child.den - frame.child.den + frame.child.num := by
          unfold ChildFrame.sGrade w1T
          rw [hu1, hu2']
          ring
        have hsy2 : frame.sGrade (c - frame.child.modifiedDeck.transverse) =
            frame.sGrade (v - frame.child.modifiedDeck.transverse) +
              (frame.child.den + frame.child.num) * (c.1 - v.1) + (frame.child.den - frame.child.num) * (c.2 - v.2) := by
          unfold ChildFrame.sGrade
          rw [transverse_eq]
          simp only [Prod.fst_sub, Prod.snd_sub]
          ring
        have hexcl : ¬ (v.1 - c.1 = -1 ∧ v.2 - c.2 = 1) := by
          rintro ⟨h1, h2⟩
          have e1 : c.1 - v.1 = 1 := by omega
          have e2 : c.2 - v.2 = -1 := by omega
          rw [e1, e2, hsuL] at hsy2
          have : frame.sGrade (c - frame.child.modifiedDeck.transverse) =
              w1T frame.child.num frame.child.den - frame.child.den + 3 * frame.child.num := by
            rw [hsy2]
            ring
          omega
        rcases hA3 with h1 | h1 | h1 <;> rcases hB3 with h2 | h2 | h2 <;> (rw [h1, h2] at htu2; omega)
      · -- `u ≠ H_{d−1}`: `t(u) + 2 ≤ d`
        have hodd_u : ¬ EvenSite (v - frame.child.modifiedDeck.transverse) := by
          unfold EvenSite
          rw [transverse_eq]
          simp only [Prod.fst_sub, Prod.snd_sub]
          omega
        have hdl := FLatticePaper.ShortRoute.freeH_tGrade_add_two_le frame hu hodd_u hL
        rcases hA3 with h1 | h1 | h1 <;> rcases hB3 with h2 | h2 | h2 <;> (rw [h1, h2] at htu2; omega)

end FLatticePaper.TopBounds
