import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.SheetRegions

/-! Task 56 (Q2, the offers of the longitudinal exits), derived from the conjugate packet.

The offers of `LongitudinalOffers` are statements about the sheets `A`, `C` of `Fp = quarterTurnField G` at `v + X`, where
`G = standardField (conjWord word)` is the earlier field. The derivation uses only the packet of the earlier word:

* the period `U_p ↦ T_e` of the quarter turn (the earlier child's transverse vector is `Z(U_p)`): `Fp` is `U_p`-periodic
  (`quarterTurnField_add_up`), since the constant `cV_e = −D − B` of the earlier child matches the harmonic shift;
* the sheet facts of `sheetFacts_of_conjPacket` (zero strip of `A`, harmonic identity on the active sheet).

This file proves the first offer for `W = 0`, with the periodicity. -/

namespace FLatticePaper.Induction
open Farey

/-- The quarter turn `Z(x) = (−x₂, x₁ − 1)` of the field's argument. -/
theorem mapSite_quarterTurn_eq (x : Site) :
    QuarterTurn.counterclockwise.mapSite (0, -1) x = (-x.2, x.1 - 1) := by
  ext <;> simp [QuarterTurn.mapSite, QuarterTurn.turn, sub_eq_add_neg]

/-- The harmonic grid along the even vector `(2D, 2N)`: `h(w + (2D, 2N)) = h(w) + s_p(w) + (B − N)`, with
`s_p(w) = (D + N) w₁ + (D − N) w₂` and `B = D² + 2DN − N²`. -/
theorem harmonicGrid_add_two (D N : ℤ) (w : Site) :
    harmonicGrid (w + (2 * D, 2 * N)) =
      harmonicGrid w + ((D + N) * w.1 + (D - N) * w.2 + (D ^ 2 + 2 * D * N - N ^ 2 - N)) := by
  obtain ⟨x1, x2⟩ := w
  unfold harmonicGrid
  simp only [Prod.fst_add, Prod.snd_add]
  have hp : (x1 + 2 * D + (x2 + 2 * N)) % 2 = (x1 + x2) % 2 := by omega
  rw [hp]
  have key : (x1 + 2 * D) ^ 2 + 2 * (x1 + 2 * D) * (x2 + 2 * N) - (x2 + 2 * N) ^ 2 - 2 * (x2 + 2 * N) - (x1 + x2) % 2
      = (x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2)
        + 4 * ((D + N) * x1 + (D - N) * x2 + (D ^ 2 + 2 * D * N - N ^ 2 - N)) := by ring
  rw [key]
  generalize x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2 = X
  generalize (D + N) * x1 + (D - N) * x2 + (D ^ 2 + 2 * D * N - N ^ 2 - N) = Y
  omega

/-- The odd parent `N / D` of the current word reads the earlier child: `num = D − N`, `den = D + N`. -/
theorem conj_child_num_den {frame conj : ChildFrame} (hconj : conj.child = frame.parents.odd.rotate) :
    conj.child.num = frame.parents.odd.den - frame.parents.odd.num ∧
      conj.child.den = frame.parents.odd.den + frame.parents.odd.num := by
  rw [hconj, Fraction.rotate_of_odd frame.valid.odd_parity]
  exact ⟨rfl, rfl⟩

/-- The periodicity of the quarter-turned earlier field along `(2D, 2N)`: the earlier child's transverse period, with the
constant `cV_e = −D − B` (from `coherentConstantV_eq`, the earlier period `2B`), cancels the harmonic shift. -/
theorem quarterTurnField_add_two {conj : ChildFrame} {G : Field}
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    {D N : ℤ} (hnum : conj.child.num = D - N) (hden : conj.child.den = D + N) (w : Site) :
    quarterTurnField G (w + (2 * D, 2 * N)) = quarterTurnField G w := by
  have hcV := conj.coherentConstantV_eq
  have hPer : conj.child.periodDenominator = 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hnum, hden]
    ring
  rw [hnum, hden, hPer] at hcV
  have hcV' : conj.coherentConstantV = -D - (D ^ 2 + 2 * D * N - N ^ 2) := by linarith
  have hTr : conj.child.modifiedDeck.transverse = (-2 * N, 2 * D) := by
    rw [conj.child_modifiedDeck_transverse, hnum, hden]
    congr 1 <;> ring
  have hZ : QuarterTurn.counterclockwise.mapSite (0, -1) (w + (2 * D, 2 * N)) =
      QuarterTurn.counterclockwise.mapSite (0, -1) w + conj.child.modifiedDeck.transverse := by
    rw [mapSite_quarterTurn_eq, mapSite_quarterTurn_eq, hTr]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  unfold quarterTurnField
  rw [hZ, hG.2, harmonicGrid_add_two, mapSite_quarterTurn_eq]
  unfold Fraction.transverseGrade
  rw [hden, hnum, hcV']
  ring

/-- The first offer for `W = 0`: the sheet `A` at `v + U_p` is `Fp(v − U_q)` (periodicity), which is at least the sheet
minimum `h(v)` (the harmonic strip), since `A(v) = Fp(v − U_q)` is one of the two sheets of the minimum. -/
theorem first_offer_of_phase_zero {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hS : frame.StripInputs (frame.sheetMin (quarterTurnField G)))
    (hW : frame.phaseW = 0) {v : Site} (hv : v ∈ frame.closedPolygon)
    (hs : frame.sGrade v ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    harmonicGrid v ≤ frame.sheetA (quarterTurnField G) (v + frame.offsetX) := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hX : frame.offsetX = (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := frame.offsetX_of_W0 hW
  have hsh : frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
    ext <;> simp [ChildFrame.sheetShift, Fraction.unmodifiedDeck, hW]
  have hA : frame.sheetMin (quarterTurnField G) v ≤ frame.sheetA (quarterTurnField G) v := by
    unfold ChildFrame.sheetMin
    exact min_le_left _ _
  rw [← hS.harmonic v hv hs, hX]
  unfold ChildFrame.sheetA at hA ⊢
  rw [hsh] at hA ⊢
  have e : v + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) - (frame.parents.even.den, frame.parents.even.num) =
      (v - (frame.parents.even.den, frame.parents.even.num)) + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
    abel
  rw [e, quarterTurnField_add_two hG hnum hden]
  exact hA

end FLatticePaper.Induction
