import FLatticePaper.Tiles.AltLatticeEvenVMain
import FLatticePaper.Tiles.AltLatticeOddWWrap

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`, even alternate child along `v_{q₀,2}`, from the family

At an uncorrected word `u x` (`x = 1, 2`), an odometer respecting the decomposition `tileAltEvenPieces` over the family below
the word, on the printed even alternate tile, is lattice self-compatible along `v_{q₀,2}` with the factor `a_{q₀,2}`. -/

namespace FLatticePaper.Tiles.AltLatticeEvenVWrap

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (JointData JSlice FirstTileNormal)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SiteInduction (curE)

/-- The odd register of `u x` (`x = 1, 2`) is `u`. -/
theorem regs1_snoc (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) : (SurgicalWeak.regsAt (u ++ [xd])).1 = some u := by
  cases xd with
  | one => rw [ConnectedAltL.regs_snoc_one]
  | two => exact ConnectedAltL.regs_snoc_two u
  | three => exact absurd rfl hx

/-- **The decomposition of the even alternate tile odometer at `u x`** (`x = 1, 2`) is `pieces7e`. -/
theorem tileAltEven_eq (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer)
    (lE : Word → Bool → Bool → PartialOdometer) (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) :
    JointFamily.tileAltEvenPieces S pO pE aO aE lE (u ++ [xd]) =
      AltGlueEven.pieces7e (u ++ [xd]) xd (pO u) (SurgicalWeak.regOdo S pO pE (SurgicalWeak.regsAt (u ++ [xd])).2 false) (aO u) := by
  have hc : decide ((u ++ [xd]).getLast? = some Digit.three) = false := by simpa using hx
  have ht : (SurgicalAlt.altTypeOf (u ++ [xd])).bind (fun ty => SurgicalAlt.altP1Coeff (JointFamily.W1Odd (u ++ [xd])) ty) =
      some (AltGlueEven.cHe (u ++ [xd]) xd) := by
    rw [AltRotStep.altTypeOf_snoc]
    cases xd with
    | three => exact absurd rfl hx
    | one => simp only [Option.bind_some, SurgicalAlt.altP1Coeff, AltGlueEven.cHe, if_true]; split_ifs <;> rfl
    | two => simp only [Option.bind_some, SurgicalAlt.altP1Coeff, AltGlueEven.cHe]; split_ifs <;> simp_all
  simp only [JointFamily.tileAltEvenPieces, hc, regs1_snoc u xd hx, ht, SurgicalWeak.regOdo, Bool.false_eq_true, if_false,
    AltGlueEven.pieces7e, List.cons_append, List.nil_append]

/-- **The data of the alternate parent piece of the even child from the family**: the odd alternate tile odometer of `u` is
defined on `altOddTile u`, contains the first tile, and has the normalised half-turn about `D̂(u)`. -/
theorem alt_odd_parent_data (D : JointData) (hAB : JointFamily.PaperAltBdry D) (f : Word → JSlice)
    (u : Word) (hJ : JointFamily.IsJointSlice D f u) (hP : JointFamily.JointProps f u)
    (hs : JointRot.SlopeZero (f u).aOdd) :
    (f u).aOdd.dom = altOddTile AltRotStep.B u ∧ ((0 : ℤ), (0 : ℤ)) ∈ (f u).aOdd.dom ∧ ((1 : ℤ), (0 : ℤ)) ∈ (f u).aOdd.dom ∧
      (∀ z ∈ (f u).aOdd.dom, JointFamily.altD u true - z ∈ (f u).aOdd.dom ∧
        2 * ((f u).aOdd.val (JointFamily.altD u true - z) - (f u).aOdd.val z) =
          dotS (JointFamily.altE u) (JointFamily.altD u true) - 2 * dotS (JointFamily.altE u) z) := by
  obtain ⟨β0, hN⟩ := hs
  obtain ⟨-, -, hT, -⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdom, -⟩ := hT
  rw [(hAB u).1] at hdom
  obtain ⟨-, hTP, -, -, -⟩ := hP
  obtain ⟨-, -, -, -, ⟨α, β, hN', hH⟩, -⟩ := hTP
  obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN' hN
  refine ⟨hdom, (hN _ (by simp [tileShape])).1, (hN _ (by simp [tileShape])).1, fun z hz => ⟨(hH z hz).1, ?_⟩⟩
  have e := (hH z hz).2
  simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at e ⊢
  linarith

set_option maxHeartbeats 400000 in
/-- **Item (b) of `lemma:weak_alternate_odometer_properties` for the even alternate child along `v_{q₀,2}`, from the family**
(words `u x` with `x = 1, 2`, the text data): an odometer respecting the decomposition `tileAltEvenPieces` over the family below
the word, defined on the printed even alternate tile, is lattice self-compatible along `v_{q₀,2}` with the factor `a_{q₀,2}`
(the second half of `JointFamily.AltLatticeEven`). -/
theorem even_V_family (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : JointFamily.PaperAltBdry D) (f : Word → JSlice) (u : Word) (xd : Digit)
    (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (hg : GoodBelow D f (u ++ [xd]).length) (o : PartialOdometer)
    (hR : JointFamily.RespectsPieces o (JointFamily.tileAltEvenPieces D.S (fun v => (JointFamily.below f (u ++ [xd]) v).tOdd) (fun v => (JointFamily.below f (u ++ [xd]) v).tEven) (fun v => (JointFamily.below f (u ++ [xd]) v).aOdd) (fun v => (JointFamily.below f (u ++ [xd]) v).aEven)
      (fun v => (JointFamily.below f (u ++ [xd]) v).lEven) (u ++ [xd])))
    (hdom : o.dom = altEvenTile AltRotStep.B (u ++ [xd])) :
    JointFamily.LatticeSelfCompatible o (texV2 ((parentsAt (u ++ [xd])).current .even))
      (offsetA ((parentsAt (u ++ [xd])).current .even).num ((parentsAt (u ++ [xd])).current .even).den true) := by
  rw [tileAltEven_eq _ _ _ _ _ _ u xd hx] at hR
  obtain ⟨-, ⟨u2, h2⟩⟩ := JointRot.regs_some _ hw
  have h1 := regs1_snoc u xd hx
  have l2 := JointInduction.regsAt_lt _ u2 (Or.inr h2)
  have lu : u.length < (u ++ [xd]).length := by simp
  rw [h2, SurgicalWeak.regOdo, JointRot.below_of_lt f _ _ l2, JointRot.below_of_lt f _ _ lu] at hR
  obtain ⟨βP, hdP0, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u lu
  obtain ⟨βQ, hdQ0, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  have hsl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv lu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨hdH, h0, h1', HH⟩ := alt_odd_parent_data D hAB f u (hg u lu).1 (hg u lu).2 hsl.2.2.1
  have hp : (parentsAt (u ++ [xd])).odd = fracOdd u := (WeakStepAssembly.regsAt_parents _).1 u h1
  have hq : (parentsAt (u ++ [xd])).even = fracEven u2 := (WeakStepAssembly.regsAt_parents _).2 u2 h2
  have htP : (stateAt (u ++ [xd])).tOdd = oddTile u := (WeakStepPaper.regsAt_tiles _).1 u h1
  have htQ : (stateAt (u ++ [xd])).tEven = evenTile u2 := (WeakStepPaper.regsAt_tiles _).2.2.1 u2 h2
  have botP0 := AltLatticeOddWWrap.std_bottom_odd D hS hA f _ hg u lu βP hcP
  have botQ0 := AltLatticeOddWWrap.std_bottom_even D hS hA f _ hg u2 l2 βQ hcQ
  refine AltLatticeEvenVMain.even_V_parents u xd hx hw (f u).tOdd (f u2).tEven (f u).aOdd (by rw [hdP0, htP])
    (by rw [hdQ0, htQ]) h0 h1' ?_ ?_ HH βP βQ ?_ ?_ ?_ ?_ ?_ ?_ o hR hdom
  · intro z hz
    obtain ⟨m, eq⟩ := hhP z hz
    simp only [AltGlueOdd.Cp, JointFamily.aP2, hp, offsetA]
    exact ⟨m, eq⟩
  · intro z hz
    obtain ⟨m, eq⟩ := hhQ z hz
    simp only [AltGlueOdd.Cq, JointFamily.aQ2, hq, offsetA]
    exact ⟨m, eq⟩
  · intro y a b
    rw [htP] at a
    rw [htP, hp] at b
    exact botP0 y a b
  · intro y a b
    rw [htQ] at a
    rw [htQ, hq] at b
    exact botQ0 y a b
  · have c := hcP.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero] at c
    linarith
  · have c := hcP.2.2.2.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at c
    rw [hp]; linarith
  · have c := hcQ.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero] at c
    linarith
  · have c := hcQ.2.2.2.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at c
    rw [hq]; linarith

end FLatticePaper.Tiles.AltLatticeEvenVWrap
