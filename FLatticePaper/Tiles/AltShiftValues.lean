import FLatticePaper.Tiles.AltShiftGeom
import FLatticePaper.Tiles.AltLatticeOddWWrap

/-! # The compatibility of a register with its translate by the alternate shift

For a non-base word `w` with registers `u₁`, `u₂`, the odd register `o_{p}` of the family is compatible with its translate by
`S_p`, and the even register `o_{q}` with its translate by `S_q`, both with the affine factor `a_{p,2}` (`shift_compat_family`).
* The odd register: the overlap is on the bottom walk, where `o_p = β`, and its translate on the top walk, where the half-turn
  of `o_p` gives `2 o_p(y) = 2β - a_{p,2}^T C_p + 2 a_{p,2}^T y` (`shift_P`).
* The even register: after a translation by `v_{q,1}` (no affine term, `TileTranslation`), both points lie on the right walk,
  where `o_q(z) + h₀(z - v_{q,1})` is constant (the quarter turn: `MixedCompatEdges.four_traces` on the side `v⁺`, through
  `rot_standard_tiles`, `right_walk_even`). The difference of `h₀` along `v_{p,2}` is linear with the coefficient
  `hHalf(v_{p,2}) = a_{p,2}` (`JointRot.h0_sub`), which cancels the affine factor (`shift_Q`). -/

namespace FLatticePaper.Tiles.AltShiftValues

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.JointFamily (JointData JSlice LatticeSelfCompatible)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.AltShiftGeom (shP shQ)

/-- A defect whose double is constant is constant. -/
theorem lattice_of_double (o : PartialOdometer) (v a : Site) (K : ℤ)
    (h : ∀ x, x ∈ o.dom → x + v ∈ o.dom → 2 * (o.val (x + v) - o.val x - dotS a x) = K) : LatticeSelfCompatible o v a := by
  by_cases hex : ∃ x, x ∈ o.dom ∧ x + v ∈ o.dom
  · obtain ⟨x0, h0, h0'⟩ := hex
    refine ⟨o.val (x0 + v) - o.val x0 - dotS a x0, fun x h1 h2 => ?_⟩
    have e1 := h x h1 h2
    have e2 := h x0 h0 h0'
    linarith
  · exact ⟨0, fun x h1 h2 => absurd ⟨x, h1, h2⟩ hex⟩

/-- **The odd register along `S_p`, from its half-turn and its bottom walk.** -/
theorem shift_P {w : Word} (hw : ¬ IsBase w) (P : PartialOdometer) (hdP : P.dom = (stateAt w).tOdd)
    (HP : ∀ z ∈ P.dom, AltGlueOdd.Cp w - z ∈ P.dom ∧
      2 * (P.val (AltGlueOdd.Cp w - z) - P.val z) = dotS (JointFamily.aP2 w) (AltGlueOdd.Cp w) - 2 * dotS (JointFamily.aP2 w) z)
    (βP : ℤ) (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP) :
    LatticeSelfCompatible P (shP w) (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) := by
  refine lattice_of_double P _ _ (-dotS (JointFamily.aP2 w) (AltGlueOdd.Cp w) + 2 * dotS (JointFamily.aP2 w) (shP w)) ?_
  intro x hx hxS
  rw [hdP] at hx hxS
  have g := AltShiftGeom.geomP hw x ((AltGlueOdd.mem_tOdd_iff hw x).1 hx) ((AltGlueOdd.mem_tOdd_iff hw _).1 hxS)
  have hxB : x + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := (AltGlueOdd.mem_tOdd_iff hw _).2 g.1
  have hxSB : x + shP w - texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := (AltGlueOdd.mem_tOdd_iff hw _).2 g.2
  have e1 := botP x hx hxB
  have hz1 : AltGlueOdd.Cp w - (x + shP w) ∈ (stateAt w).tOdd := by
    rw [← hdP]; exact (HP _ (by rw [hdP]; exact hxS)).1
  have hz2 : AltGlueOdd.Cp w - (x + shP w) + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := by
    have h := (HP _ (by rw [hdP]; exact hxSB)).1
    rw [hdP] at h
    have e : AltGlueOdd.Cp w - (x + shP w - texV2 (parentsAt w).odd) = AltGlueOdd.Cp w - (x + shP w) + texV2 (parentsAt w).odd := by
      abel
    rwa [e] at h
  have e2 := botP _ hz1 hz2
  have hH := (HP _ (by rw [hdP]; exact hz1)).2
  rw [sub_sub_cancel, e2] at hH
  rw [show offsetA (parentsAt w).odd.num (parentsAt w).odd.den true = JointFamily.aP2 w from rfl, e1]
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hH ⊢
  linarith

/-- `hHalf(v_{p,2}) = a_{p,2}`. -/
theorem hHalf_texV2 (f : Fraction) : JointRot.hHalf (texV2 f) = offsetA f.num f.den true := by
  ext <;> simp only [JointRot.hHalf, texV2, offsetA] <;> omega

/-- **The even register along `S_q`, from its right-walk heights and its first period.** -/
theorem shift_Q {w : Word} (hw : ¬ IsBase w) (Q : PartialOdometer) (hdQ : Q.dom = (stateAt w).tEven) (k : ℤ)
    (hRW : ∀ z, z ∈ (stateAt w).tEven → z - texV1Even (parentsAt w).even ∈ (stateAt w).tEven →
      Q.val z + JointFamily.h0 (z - texV1Even (parentsAt w).even) = k)
    (hper : ∀ z, z ∈ (stateAt w).tEven → z + texV1Even (parentsAt w).even ∈ (stateAt w).tEven →
      Q.val (z + texV1Even (parentsAt w).even) = Q.val z) :
    LatticeSelfCompatible Q (shQ w) (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) := by
  have hB : FLatticePaper.EvenSite (texV2 (parentsAt w).odd) := by
    change ((parentsAt w).odd.num - (parentsAt w).odd.den + ((parentsAt w).odd.num + (parentsAt w).odd.den)) % 2 = 0
    omega
  have ha := hHalf_texV2 (parentsAt w).odd
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h
  · -- `W₁` odd: `S_q = v_{q,1} + v_{p,2}`
    have hph : phase w = 1 := by simpa using h
    have hS : shQ w = texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
      simp only [shQ, h, SurgicalDict.altShifts, if_true]
    refine ⟨Construction.centeredQuarterTurnCorrection (texV2 (parentsAt w).odd), fun x hx hxS => ?_⟩
    rw [hdQ] at hx hxS
    have g := (AltShiftGeom.geomQ hw x ((AltGlueOdd.mem_tEven_iff hw x).1 hx) ((AltGlueOdd.mem_tEven_iff hw _).1 hxS)).1 hph
    have hxU : x + texV1Even (parentsAt w).even ∈ (stateAt w).tEven := (AltGlueOdd.mem_tEven_iff hw _).2 g.1
    have hxSU : x + shQ w - texV1Even (parentsAt w).even ∈ (stateAt w).tEven := (AltGlueOdd.mem_tEven_iff hw _).2 g.2
    have e0 := hper x hx hxU
    have e1 := hRW _ hxU (by rwa [add_sub_cancel_right])
    have e2 := hRW _ hxS hxSU
    rw [add_sub_cancel_right] at e1
    have e3 := JointRot.h0_sub (x + shQ w - texV1Even (parentsAt w).even) _ hB
    rw [hS, show x + (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) - texV1Even (parentsAt w).even -
      texV2 (parentsAt w).odd = x by abel, ha] at e3
    rw [hS] at e2 ⊢
    rw [show x + (texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) - texV1Even (parentsAt w).even =
      x + texV2 (parentsAt w).odd by abel] at e2 e3
    simp only [dotS, Prod.fst_add, Prod.snd_add] at e3 ⊢
    linarith
  · -- `W₁` even: `S_q = -v_{q,1} + v_{p,2}`
    have hph : phase w ≠ 1 := by simpa using h
    have hS : shQ w = -texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
      simp only [shQ, h, SurgicalDict.altShifts, Bool.false_eq_true, if_false]
    refine ⟨-dotS (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) (texV1Even (parentsAt w).even) +
      Construction.centeredQuarterTurnCorrection (texV2 (parentsAt w).odd), fun x hx hxS => ?_⟩
    rw [hdQ] at hx hxS
    have g := (AltShiftGeom.geomQ hw x ((AltGlueOdd.mem_tEven_iff hw x).1 hx) ((AltGlueOdd.mem_tEven_iff hw _).1 hxS)).2 hph
    have hxU : x - texV1Even (parentsAt w).even ∈ (stateAt w).tEven := (AltGlueOdd.mem_tEven_iff hw _).2 g.1
    have hxSU : x + shQ w + texV1Even (parentsAt w).even ∈ (stateAt w).tEven := (AltGlueOdd.mem_tEven_iff hw _).2 g.2
    have e0 := hper _ hxS hxSU
    have e1 := hRW _ hx hxU
    have e2 := hRW _ hxSU (by rwa [add_sub_cancel_right])
    rw [add_sub_cancel_right] at e2
    have e3 := JointRot.h0_sub (x + shQ w) _ hB
    rw [hS, show x + (-texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) - texV2 (parentsAt w).odd =
      x - texV1Even (parentsAt w).even by abel, ha] at e3
    rw [hS] at e0 e2 ⊢
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at e3 ⊢
    linarith

end FLatticePaper.Tiles.AltShiftValues
