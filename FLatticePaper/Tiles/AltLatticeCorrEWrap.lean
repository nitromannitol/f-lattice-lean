import FLatticePaper.Tiles.AltLatticeCorrE
import FLatticePaper.Tiles.AltLatticeOddWWrap

/-! # Item (b) of `lemma:weak_alternate_odometer_properties` at the corrected even child, from the family

At `w = u 3` the even alternate tile odometer is the decomposition `tileAltEvenPieces` with the elongated even L-corrections of
`u` in place of `T(q₁)^{+,1}` and `T(q₁)^{-,2}`. With its half-turn (b), slope zero (`JointRot.slope_tileAltEven`) and the
agreement of `o^{L,+}_{q₁}` with `o_{q₁}` on the bottom string (`LSidesAgree`, `lemma:l_correct_existence`), it is lattice
self-compatible along `v_{q₀,2}`. -/

namespace FLatticePaper.Tiles.AltLatticeCorrEWrap

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (JointData JSlice FirstTileNormal stdPiece altOff altAff W1Odd)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SiteInduction (curE)

theorem altD_false (w : Word) : JointFamily.altD w false = AltGlueEven.De w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    simp only [JointFamily.altD, AltGlueEven.De, h] <;> ext <;>
    simp [JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2,
      AltPieces.centreEven] <;> ring

/-- The normalised half-turn with slope zero. -/
theorem halfTurnId_of_alt (o : PartialOdometer) (Dh E : Site) (hT : JointFamily.AltHalfTurn o Dh E)
    (hs : JointRot.SlopeZero o) : AltLatticeCore.HalfTurnId o Dh (-(2 : ℤ) • E) (dotS E Dh) := by
  obtain ⟨α, β, hN, hH⟩ := hT
  obtain ⟨β0, hN0⟩ := hs
  obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN hN0
  intro x hx
  refine ⟨(hH x hx).1, ?_⟩
  have e := (hH x hx).2
  simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at e ⊢
  linarith

set_option maxHeartbeats 400000 in
/-- **Item (b) at the corrected even child, along `v_{q₀,2}`, from the family** (`w = u 3`, the text data): an odometer respecting
`tileAltEvenPieces` over the family below `w`, on the printed even alternate tile, with the half-turn (b) of the even alternate tile
odometer, is lattice self-compatible along `v_{q₀,2}` with the factor `a_{q₀,2}`. -/
theorem even_V_corr_family (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = JointFamily.paperLSides) (f : Word → JSlice) (u : Word) (hw : ¬ IsBase (u ++ [Digit.three]))
    (hg : GoodBelow D f (u ++ [Digit.three]).length) (o : PartialOdometer)
    (hR : JointFamily.RespectsPieces o (JointFamily.tileAltEvenPieces D.S (fun v => (JointFamily.below f (u ++ [Digit.three]) v).tOdd) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).tEven) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).aOdd) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).aEven)
      (fun v => (JointFamily.below f (u ++ [Digit.three]) v).lEven) (u ++ [Digit.three])))
    (hdom : o.dom = altEvenTile AltRotStep.B (u ++ [Digit.three])) (hHT : JointFamily.AltHalfTurn o (JointFamily.altD (u ++ [Digit.three]) false) (JointFamily.altE (u ++ [Digit.three]))) :
    JointFamily.LatticeSelfCompatible o (texV2 ((parentsAt (u ++ [Digit.three])).current .even))
      (offsetA ((parentsAt (u ++ [Digit.three])).current .even).num ((parentsAt (u ++ [Digit.three])).current .even).den true) := by
  have lu : u.length < (u ++ [Digit.three]).length := by simp
  have hdrop : (u ++ [Digit.three]).dropLast = u := List.dropLast_concat
  have hJu := hg u lu
  -- the L-correction and its agreement with the even child of `u` on the bottom string
  have hdef : JointFamily.EvenLDefined u := by
    refine JointRot.evenLDefined_of_mem _ ?_
    by_contra hc
    refine hw (Or.inr (Or.inl fun d hd => ?_))
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · by_contra hne
      exact hc ⟨d, hd, hne⟩
    · rfl
  obtain ⟨hRL, hAg⟩ := hJu.1.2.2.2.2 true true hdef
  obtain ⟨-, c, hc⟩ := hAg
  have hside : Side.hPlus ∈ D.lSides false (W1Odd u) true true := by
    rw [hlS]; cases W1Odd u <;> simp [JointFamily.paperLSides, JointFamily.printedEvenSides]
  obtain ⟨βQ, hdQ0, hcQ, -⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u lu
  have botQ0 := AltLatticeOddWWrap.std_bottom_even D hS hA f _ hg u lu βQ hcQ
  have hq : (parentsAt (u ++ [Digit.three])).even = fracEven u := (HorizontalStep.par_three u).2
  have htQ : (stateAt (u ++ [Digit.three])).tEven = evenTile u := (HorizontalStep.reg_three u).2
  have botL : ∀ y, y ∈ (stateAt (u ++ [Digit.three])).tEven → y + texV2 (parentsAt (u ++ [Digit.three])).even ∈ (stateAt (u ++ [Digit.three])).tEven →
      y ∈ ((f u).lEven true true).dom ∧ ((f u).lEven true true).val y = βQ + c := by
    intro y a b
    rw [htQ] at a
    rw [htQ, hq] at b
    have hb := OverlapSides.even_bottom_of_overlap u y a (by rwa [sub_neg_eq_add])
    have e : StandardBoundary.evenBottom u = gH (hWordOf u true) := RegisterLink.evenBottom_eq_gH u
    have hs := HBottom.hB_even u y hb
    have hp := (StdPseudoAnchoredSets.placed_hStringAt_iff _ y).2 hs
    obtain ⟨m, -, ev⟩ := hc _ hside y hp
    refine ⟨m, ?_⟩
    rw [ev, botQ0 y a b]
  -- the values on the first piece
  have hmem : stdPiece ((f u).lEven true true) (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) (altAff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) ∈ JointFamily.tileAltEvenPieces D.S (fun v => (JointFamily.below f (u ++ [Digit.three]) v).tOdd) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).tEven)
      (fun v => (JointFamily.below f (u ++ [Digit.three]) v).aOdd) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).aEven) (fun v => (JointFamily.below f (u ++ [Digit.three]) v).lEven) (u ++ [Digit.three]) := by
    have hc3 : decide ((u ++ [Digit.three]).getLast? = some Digit.three) = true := by simp
    simp only [JointFamily.tileAltEvenPieces, hc3, if_true, hdrop, JointRot.below_of_lt f _ _ lu]
    simp
  obtain ⟨κ0, hκ0⟩ := AltGlueOdd.respects_std o _ hR _ _ _ hmem
  have hv0 : ∀ y, y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) ∈ ((f u).lEven true true).dom → o.val y = ((f u).lEven true true).val (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) +
      dotS (altAff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) y + κ0 := by
    intro y hy
    rw [hκ0 y (by rw [AltGlueHalfTurn.mem_placed_iff]; exact hy)]; rfl
  -- slope zero and the normalised half-turn
  obtain ⟨⟨u1, h1⟩, ⟨u2, h2⟩⟩ := JointRot.regs_some _ hw
  have l1 := JointInduction.regsAt_lt _ u1 (Or.inl h1)
  have l2 := JointInduction.regsAt_lt _ u2 (Or.inr h2)
  have sl := fun (k : Word) (hk : k.length < (u ++ [Digit.three]).length) => JointRot.family_slopes D f k.length
    (fun v hv => (hg v (lt_of_le_of_lt hv hk)).1) (JointRot.baseSlopes_paper D hS hA) k le_rfl
  have hs : JointRot.SlopeZero o := by
    refine JointRot.slope_tileAltEven _ _ _ _ _ _ (u ++ [Digit.three]) o hR ?_ ?_ (fun hW _ => ?_)
    · rw [h1]; show JointRot.SlopeZero (JointFamily.below f (u ++ [Digit.three]) u1).tOdd
      rw [JointRot.below_of_lt f _ _ l1]; exact (sl u1 l1).1
    · rw [h2]; show JointRot.SlopeZero (JointFamily.below f (u ++ [Digit.three]) u2).tEven
      rw [JointRot.below_of_lt f _ _ l2]; exact (sl u2 l2).2.1
    · rw [hdrop, JointRot.below_of_lt f _ _ lu]
      have hW' : W1Odd u = false := by
        have hph := AltItem4.phase_snoc_three u
        unfold W1Odd at hW ⊢
        rw [← hph]; exact hW
      refine JointRot.slope_evenL _ _ _ _ _ u _ hRL hW' ?_
      cases h : (SurgicalWeak.regsAt (JointFamily.stripTrailing Digit.three u)).2 with
      | none => exact (JointRot.baseSlopes_paper D hS hA).2
      | some v =>
        have lv := JointInduction.regsAt_lt _ v (Or.inr h)
        have lp := JointRot.stripTrailing_length_le Digit.three u
        show JointRot.SlopeZero (JointFamily.below f u v).tEven
        rw [JointRot.below_of_lt f u v (by omega)]
        exact (sl v (by omega)).2.1
  have HT := halfTurnId_of_alt o _ _ hHT hs
  rw [altD_false] at HT
  exact AltLatticeCorrE.even_V_corr u hw _ o (βQ + c) κ0 botL hv0 HT hdom

end FLatticePaper.Tiles.AltLatticeCorrEWrap
