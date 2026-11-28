import FLatticePaper.Tiles.TileHalfTurnCorr

/-! # `TileStepAssembly.HalfTurnInput` for the paper data

(b) of `lemma:tile-odometer-existence` at every non-base word `w = u x`, from the family below `w`: the parents (shorter words)
have their half-turn identities and are normalised with slope `0` (`JointRot.family_slopes`); the tile odometers at `w` respect
their decompositions (`TilePart`), whose overlap graphs are connected (`JointRot.std_connected`, `ConnectedAltL.connectedAlt_of`);
the L-corrected odometers of `u` respect theirs (`LPart`), connected by `ConnectedL.connectedL_of`. After a `1` all four children
are Cases 1 and 3; after a `2` the even standard and the odd alternate child are corrected (Cases 2 and 4 with the odd
L-corrections of `u`), after a `3` the odd standard and the even alternate child (with the even L-corrections of `u`).

The half-turn of the L-corrected odometers at the prefixes `2^j` (even) and `3^j` (odd) is the named input `SpecialLHalfTurn`. -/

namespace FLatticePaper.Tiles.TileHalfTurnInput

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.TileStepAssembly (tOP tEP aOP aEP HalfTurnInput)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.TileHalfTurnStd (RawHT)
open FLatticePaper.Tiles.TileHalfTurnCorr (CrossHT)
open FLatticePaper.Tiles.JointRot (SlopeZero)

/-- **Named input**: the half-turn of the L-corrected odometers at the special prefixes, `w₁ s = 2^j` for the even and `3^j`
for the odd L-corrections (the zero-one odometers and the exceptional points of the first heads). -/
def SpecialLHalfTurn (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (u : Word), GoodBelow D f (u.length + 1) →
    (EvenLDefined u → (stripTrailing Digit.three u ≠ [] ∧ ∀ d ∈ stripTrailing Digit.three u, d = Digit.two) →
      ∀ b elong : Bool, CrossHT ((f u).lEven b elong) ((f u).lEven (!b) elong)
        (TileHalfTurnStd.cEven ((parentsAt u).current .even)) (TileHalfTurnStd.aF ((parentsAt u).current .even))) ∧
    (OddLDefined u → (stripTrailing Digit.two u ≠ [] ∧ ∀ d ∈ stripTrailing Digit.two u, d = Digit.three) →
      ∀ b elong : Bool, CrossHT ((f u).lOdd b elong) ((f u).lOdd (!b) elong)
        (TileHalfTurnStd.cOdd ((parentsAt u).current .odd)) (TileHalfTurnStd.aF ((parentsAt u).current .odd)))

/-! ### The family below a word -/

theorem slopes_below (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hG : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    SlopeZero (f u).tOdd ∧ SlopeZero (f u).tEven ∧ SlopeZero (f u).aOdd ∧ SlopeZero (f u).aEven :=
  JointRot.family_slopes D f (n - 1) (fun v hv => (hG v (by omega)).1) (JointRot.baseSlopes_paper D hS hA) u (by omega)

theorem raw_below (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hG : GoodBelow D f n) (u : Word) (hu : u.length < n) :
    RawHT (f u).tOdd (TileHalfTurnStd.cOdd ((parentsAt u).current .odd)) (TileHalfTurnStd.aF ((parentsAt u).current .odd)) ∧
    RawHT (f u).tEven (TileHalfTurnStd.cEven ((parentsAt u).current .even))
      (TileHalfTurnStd.aF ((parentsAt u).current .even)) ∧
    RawHT (f u).aOdd (altD u true) (altE u) ∧ RawHT (f u).aEven (altD u false) (altE u) := by
  obtain ⟨s1, s2, s3, s4⟩ := slopes_below D hS hA f n hG u hu
  obtain ⟨-, -, h1, h2, h3, h4⟩ := (hG u hu).2.2.1
  exact ⟨TileHalfTurnStd.raw_of_tileHalfTurn _ _ _ _ h1 s1, TileHalfTurnStd.raw_of_tileHalfTurn _ _ _ _ h2 s2,
    TileHalfTurnStd.raw_of_altHalfTurn _ _ _ h3 s3, TileHalfTurnStd.raw_of_altHalfTurn _ _ _ h4 s4⟩

theorem raw_reg_odd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hG : GoodBelow D f n) (x r : Word) (hr : (regsAt x).1 = some r) (hrl : r.length < n) :
    RawHT (f r).tOdd (TileHalfTurnStd.cOdd (parentsAt x).odd) (TileHalfTurnStd.aF (parentsAt x).odd) := by
  rw [(WeakStepAssembly.regsAt_parents x).1 r hr]
  exact (raw_below D hS hA f n hG r hrl).1

theorem raw_reg_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hG : GoodBelow D f n) (x r : Word) (hr : (regsAt x).2 = some r) (hrl : r.length < n) :
    RawHT (f r).tEven (TileHalfTurnStd.cEven (parentsAt x).even) (TileHalfTurnStd.aF (parentsAt x).even) := by
  rw [(WeakStepAssembly.regsAt_parents x).2 r hr]
  exact (raw_below D hS hA f n hG r hrl).2.1

theorem strip_of (d s : Digit) (hs : s ≠ d) (w1 : Word) (k : ℕ) :
    stripTrailing d (w1 ++ [s] ++ List.replicate k d) = w1 ++ [s] := by
  induction k with
  | zero => simp [JointRot.stripTrailing_snoc, hs]
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, JointRot.stripTrailing_snoc, if_pos rfl, ih]

theorem length_strip_lt {d s : Digit} {w1 : Word} {k : ℕ} {u : Word} (hu : u = w1 ++ [s] ++ List.replicate k d) :
    w1.length < u.length := by
  rw [hu]; simp

/-! ### The half-turns of the L-corrected odometers of a word -/

/-- The even L-corrected odometers of `u`, from the family up to `u`. -/
theorem crossEven (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hspec : SpecialLHalfTurn D) (f : Word → JSlice) (u : Word) (hG : GoodBelow D f (u.length + 1))
    (hdef : EvenLDefined u) (b elong : Bool) :
    CrossHT ((f u).lEven b elong) ((f u).lEven (!b) elong) (TileHalfTurnStd.cEven ((parentsAt u).current .even))
      (TileHalfTurnStd.aF ((parentsAt u).current .even)) := by
  obtain ⟨w1, s, k, hs, hu⟩ := id hdef
  have hpre : stripTrailing Digit.three u = w1 ++ [s] := by rw [hu]; exact strip_of _ _ hs _ _
  have hw1 : w1.length < u.length := length_strip_lt hu
  by_cases hsp : ∀ d ∈ stripTrailing Digit.three u, d = Digit.two
  · exact (hspec f u hG).1 hdef ⟨by rw [hpre]; simp, hsp⟩ b elong
  have hreg : (!(stripTrailing Digit.three u).isEmpty &&
      (stripTrailing Digit.three u).all (fun d => decide (d = Digit.two))) = false := by
    cases h : (stripTrailing Digit.three u).all (fun d => decide (d = Digit.two)) with
    | false => simp
    | true => exact absurd (fun d hd => by simpa using List.all_eq_true.1 h d hd) hsp
  have hJu : IsJointSlice D f u := (hG u (by omega)).1
  have hG' : GoodBelow D f u.length := fun v hv => hG v (by omega)
  have hRs := (hJu.2.2.2.2 b elong hdef).1
  have hRt := (hJu.2.2.2.2 (!b) elong hdef).1
  have hconn := (ConnectedL.connectedL_of D hS hA f u (fun v hv => (hG' v hv).1) (fun v hv => (hG' v hv).2.2.1)).2 b elong hdef
  have hr1 : (regsAt (stripTrailing Digit.three u)).1 = some w1 := by rw [hpre]; exact ConnectedAltL.regs_pre_fst w1 s hs
  obtain ⟨y, hr2⟩ : ∃ y, (regsAt (stripTrailing Digit.three u)).2 = some y := by
    cases h : (regsAt (stripTrailing Digit.three u)).2 with
    | none => exact absurd ((WeakStepAssembly.regsAt_snd_none _).1 h) hsp
    | some y => exact ⟨y, rfl⟩
  have hy : y.length < u.length :=
    lt_of_lt_of_le (regsAt_lt _ y (Or.inr hr2)) (JointRot.stripTrailing_length_le _ _)
  have hSt : RawHT (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
      (regsAt (stripTrailing Digit.three u)).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.three u)).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).odd) := by
    rw [hr1]
    show RawHT (below f u w1).tOdd _ _
    rw [JointRot.below_of_lt f u w1 hw1]
    exact raw_reg_odd D hS hA f u.length hG' _ w1 hr1 hw1
  have hBr : RawHT (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
      (regsAt (stripTrailing Digit.three u)).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.three u)).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.three u)).even) := by
    rw [hr2]
    show RawHT (below f u y).tEven _ _
    rw [JointRot.below_of_lt f u y hy]
    exact raw_reg_even D hS hA f u.length hG' _ y hr2 hy
  have hHd : RawHT (regOdo D.S (fun v => (below f u v).aOdd) (fun v => (below f u v).aEven)
      (regsAt (stripTrailing Digit.three u)).1 true) (altD w1 true) (altE w1) := by
    rw [hr1]
    show RawHT (below f u w1).aOdd _ _
    rw [JointRot.below_of_lt f u w1 hw1]
    exact (raw_below D hS hA f u.length hG' w1 hw1).2.2.1
  exact TileHalfTurnL.lHalfTurn_even D.S _ _ _ _ u w1 s hs hpre hreg b elong _ _ hRs hRt hconn hSt hBr hHd

/-- The odd L-corrected odometers of `u`, from the family up to `u`. -/
theorem crossOdd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hspec : SpecialLHalfTurn D) (f : Word → JSlice) (u : Word) (hG : GoodBelow D f (u.length + 1))
    (hdef : OddLDefined u) (b elong : Bool) :
    CrossHT ((f u).lOdd b elong) ((f u).lOdd (!b) elong) (TileHalfTurnStd.cOdd ((parentsAt u).current .odd))
      (TileHalfTurnStd.aF ((parentsAt u).current .odd)) := by
  obtain ⟨w1, s, k, hs, hu⟩ := id hdef
  have hpre : stripTrailing Digit.two u = w1 ++ [s] := by rw [hu]; exact strip_of _ _ hs _ _
  have hw1 : w1.length < u.length := length_strip_lt hu
  by_cases hsp : ∀ d ∈ stripTrailing Digit.two u, d = Digit.three
  · exact (hspec f u hG).2 hdef ⟨by rw [hpre]; simp, hsp⟩ b elong
  have hreg : (!(stripTrailing Digit.two u).isEmpty &&
      (stripTrailing Digit.two u).all (fun d => decide (d = Digit.three))) = false := by
    cases h : (stripTrailing Digit.two u).all (fun d => decide (d = Digit.three)) with
    | false => simp
    | true => exact absurd (fun d hd => by simpa using List.all_eq_true.1 h d hd) hsp
  have hJu : IsJointSlice D f u := (hG u (by omega)).1
  have hG' : GoodBelow D f u.length := fun v hv => hG v (by omega)
  have hRs := (hJu.2.2.2.1 b elong hdef).1
  have hRt := (hJu.2.2.2.1 (!b) elong hdef).1
  have hconn := (ConnectedL.connectedL_of D hS hA f u (fun v hv => (hG' v hv).1) (fun v hv => (hG' v hv).2.2.1)).1 b elong hdef
  have hr2 : (regsAt (stripTrailing Digit.two u)).2 = some w1 := by rw [hpre]; exact ConnectedAltL.regs_pre_snd w1 s hs
  obtain ⟨y, hr1⟩ : ∃ y, (regsAt (stripTrailing Digit.two u)).1 = some y := by
    cases h : (regsAt (stripTrailing Digit.two u)).1 with
    | none => exact absurd ((WeakStepAssembly.regsAt_fst_none _).1 h) hsp
    | some y => exact ⟨y, rfl⟩
  have hy : y.length < u.length :=
    lt_of_lt_of_le (regsAt_lt _ y (Or.inl hr1)) (JointRot.stripTrailing_length_le _ _)
  have hSt : RawHT (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
      (regsAt (stripTrailing Digit.two u)).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.two u)).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).even) := by
    rw [hr2]
    show RawHT (below f u w1).tEven _ _
    rw [JointRot.below_of_lt f u w1 hw1]
    exact raw_reg_even D hS hA f u.length hG' _ w1 hr2 hw1
  have hBr : RawHT (regOdo D.S (fun v => (below f u v).tOdd) (fun v => (below f u v).tEven)
      (regsAt (stripTrailing Digit.two u)).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.two u)).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two u)).odd) := by
    rw [hr1]
    show RawHT (below f u y).tOdd _ _
    rw [JointRot.below_of_lt f u y hy]
    exact raw_reg_odd D hS hA f u.length hG' _ y hr1 hy
  have hHd : RawHT (regOdo D.S (fun v => (below f u v).aOdd) (fun v => (below f u v).aEven)
      (regsAt (stripTrailing Digit.two u)).2 false) (altD w1 false) (altE w1) := by
    rw [hr2]
    show RawHT (below f u w1).aEven _ _
    rw [JointRot.below_of_lt f u w1 hw1]
    exact (raw_below D hS hA f u.length hG' w1 hw1).2.2.2
  exact TileHalfTurnL.lHalfTurn_odd D.S _ _ _ _ u w1 s hs hpre hreg b elong _ _ hRs hRt hconn hSt hBr hHd

/-! ### The assembly -/

theorem slope_aev (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (u : Word) (x : Digit) (hG : GoodBelow D f (u ++ [x]).length) (hb : ¬ IsBase (u ++ [x]))
    (o : PartialOdometer) (hR : RespectsPieces o (aEP D f (u ++ [x])))
    (hPs : SlopeZero (regOdo D.S (fun v => (below f (u ++ [x]) v).tOdd) (fun v => (below f (u ++ [x]) v).tEven)
      (regsAt (u ++ [x])).1 true))
    (hQs : SlopeZero (regOdo D.S (fun v => (below f (u ++ [x]) v).tOdd) (fun v => (below f (u ++ [x]) v).tEven)
      (regsAt (u ++ [x])).2 false)) : SlopeZero o := by
  refine JointRot.slope_tileAltEven _ _ _ _ _ _ _ o hR hPs hQs (fun hW hl => ?_)
  have hx : x = Digit.three := by simpa using hl
  subst hx
  have hul : u.length < (u ++ [Digit.three]).length := by simp
  have edl : (u ++ [Digit.three]).dropLast = u := by simp
  show SlopeZero ((below f (u ++ [Digit.three]) (u ++ [Digit.three]).dropLast).lEven true true)
  rw [edl, JointRot.below_of_lt f _ u hul]
  have hdef : EvenLDefined u := JointRot.evenLDefined_of_mem u (by
    by_contra hc
    simp only [not_exists, not_and, ne_eq, not_not] at hc
    refine hb (Or.inr (Or.inl fun d hd => ?_))
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact hc d hd
    · rfl)
  have hRL := ((hG u hul).1.2.2.2.2 true true hdef).1
  have hW' : W1Odd u = false := by
    have hph := JointRot.phase_snoc_three u
    unfold W1Odd at hW ⊢
    rw [← hph]
    exact hW
  refine JointRot.slope_evenL _ _ _ _ _ u _ hRL hW' ?_
  cases h : (regsAt (stripTrailing Digit.three u)).2 with
  | none => exact (JointRot.baseSlopes_paper D hS hA).2
  | some v =>
    have lv := regsAt_lt _ v (Or.inr h)
    have lp := JointRot.stripTrailing_length_le Digit.three u
    show SlopeZero (below f u v).tEven
    rw [JointRot.below_of_lt f u v (by omega)]
    exact (slopes_below D hS hA f _ hG v (by simp; omega)).2.1

/-- **`HalfTurnInput` for the paper data**, given the half-turn of the L-corrected odometers at the special prefixes. -/
theorem halfTurnInput_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (hlS : D.lSides = paperLSides) (hspec : SpecialLHalfTurn D) :
    HalfTurnInput D := by
  intro f w wo we wao wae tod tev aod aev hG hb _ _ hTP
  obtain ⟨u, x, rfl⟩ : ∃ u x, w = u ++ [x] := by
    rcases List.eq_nil_or_concat w with h | ⟨u, x, h⟩
    · exact absurd (Or.inl h) hb
    · exact ⟨u, x, by simpa using h⟩
  have hJ : ∀ v : Word, v.length < (u ++ [x]).length → IsJointSlice D f v := fun v hv => (hG v hv).1
  have hT : ∀ v : Word, v.length < (u ++ [x]).length → TileProps v (f v).tOdd (f v).tEven (f v).aOdd (f v).aEven :=
    fun v hv => (hG v hv).2.2.1
  have hGu : GoodBelow D f (u.length + 1) := by simpa using hG
  have hul : u.length < (u ++ [x]).length := by simp
  have edl : (u ++ [x]).dropLast = u := by simp
  obtain ⟨u1, u2, hr, hl1, hl2, -, -, -, -, -, -⟩ := StdPairCompatPaper.regs_data D hS f _ hG hb
  obtain ⟨rO, rE, rAO, rAE⟩ := hTP.2.1 hb
  obtain ⟨cO, cE⟩ := JointRot.std_connected D hlS f _ hb hJ
  obtain ⟨cAO, cAE⟩ := ConnectedAltL.connectedAlt_of D hlS f _ hb hJ hT
  have hP := raw_reg_odd D hS hA f _ hG _ u1 (by rw [hr]) hl1
  have hQ := raw_reg_even D hS hA f _ hG _ u2 (by rw [hr]) hl2
  have hPs : SlopeZero (regOdo D.S (fun v => (below f (u ++ [x]) v).tOdd) (fun v => (below f (u ++ [x]) v).tEven)
      (regsAt (u ++ [x])).1 true) := by
    rw [hr]
    show SlopeZero (below f _ u1).tOdd
    rw [JointRot.below_of_lt f _ u1 hl1]
    exact (slopes_below D hS hA f _ hG u1 hl1).1
  have hQs : SlopeZero (regOdo D.S (fun v => (below f (u ++ [x]) v).tOdd) (fun v => (below f (u ++ [x]) v).tEven)
      (regsAt (u ++ [x])).2 false) := by
    rw [hr]
    show SlopeZero (below f _ u2).tEven
    rw [JointRot.below_of_lt f _ u2 hl2]
    exact (slopes_below D hS hA f _ hG u2 hl2).2.1
  have sO := JointRot.slope_tileOdd _ _ _ _ _ tod rO hPs hQs
  have sE := JointRot.slope_tileEven _ _ _ _ _ tev rE hPs hQs
  have sAO := JointRot.slope_tileAltOdd _ _ _ _ _ _ _ aod rAO hPs hQs
  have sAE := slope_aev D hS hA f u x hG hb aev rAE hPs hQs
  have y0 : ∀ o : PartialOdometer, SlopeZero o → ((0 : ℤ), (0 : ℤ)) ∈ o.dom :=
    fun o ⟨_, hF⟩ => (hF _ (by simp [tileShape])).1
  have hH := raw_below D hS hA f _ hG u hul
  have hnotb3 : x = Digit.three → EvenLDefined u := fun hx => JointRot.evenLDefined_of_mem u (by
    by_contra hc
    simp only [not_exists, not_and, ne_eq, not_not] at hc
    refine hb (Or.inr (Or.inl fun d hd => ?_))
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact hc d hd
    · exact hx)
  have hnotb2 : x = Digit.two → OddLDefined u := fun hx => JointRot.oddLDefined_of_mem u (by
    by_contra hc
    simp only [not_exists, not_and, ne_eq, not_not] at hc
    refine hb (Or.inr (Or.inr fun d hd => ?_))
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact hc d hd
    · exact hx)
  refine ⟨TileHalfTurnStd.tileHalfTurn_of_raw _ _ _ _ sO ?_, TileHalfTurnStd.tileHalfTurn_of_raw _ _ _ _ sE ?_,
    TileHalfTurnStd.altHalfTurn_of_raw _ _ _ sAO ?_, TileHalfTurnStd.altHalfTurn_of_raw _ _ _ sAE ?_⟩
  · by_cases h3 : x = Digit.three
    · subst h3
      have e : (parentsAt (u ++ [Digit.three])).even = (parentsAt u).current .even := by
        rw [CeilWords.parentsAt_snoc_three]
      refine TileHalfTurnCorr.halfTurn_oddStd_corr D f _ u1 u2 hr hl1 hl2 (by simp) tod rO cO hP hQ ?_ ?_ (y0 _ sO)
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossEven D hS hA hspec f u hGu (hnotb3 rfl) true false
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossEven D hS hA hspec f u hGu (hnotb3 rfl) false false
    · exact TileHalfTurnStd.halfTurn_oddStd D f _ u1 u2 hr hl1 hl2 (by simpa using h3) tod rO cO hP hQ (y0 _ sO)
  · by_cases h2 : x = Digit.two
    · subst h2
      have e : (parentsAt (u ++ [Digit.two])).odd = (parentsAt u).current .odd := by
        rw [CeilWords.parentsAt_snoc_two]
      refine TileHalfTurnCorr.halfTurn_evenStd_corr D f _ u1 u2 hr hl1 hl2 (by simp) tev rE cE hP hQ ?_ ?_ (y0 _ sE)
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossOdd D hS hA hspec f u hGu (hnotb2 rfl) true false
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossOdd D hS hA hspec f u hGu (hnotb2 rfl) false false
    · exact TileHalfTurnStd.halfTurn_evenStd D f _ u1 u2 hr hl1 hl2 (by simpa using h2) tev rE cE hP hQ (y0 _ sE)
  · by_cases h2 : x = Digit.two
    · subst h2
      have e : (parentsAt (u ++ [Digit.two])).odd = (parentsAt u).current .odd := by
        rw [CeilWords.parentsAt_snoc_two]
      refine TileHalfTurnCorr.halfTurn_altOdd_corr D f _ u1 u2 hr hl1 hl2 (by simp) aod rAO cAO hP hQ ?_ ?_ (y0 _ sAO)
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossOdd D hS hA hspec f u hGu (hnotb2 rfl) true true
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossOdd D hS hA hspec f u hGu (hnotb2 rfl) false true
    · have hu2 : u2 = u := by
        have h := ConnectedAltL.regs_pre_snd u x h2
        rw [hr] at h
        exact Option.some.inj h
      subst hu2
      exact TileHalfTurnAlt.halfTurn_altOdd D f u2 x h2 u1 (by rw [hr]) hl1 aod rAO cAO hP hQ hH.2.2.2 (y0 _ sAO)
  · by_cases h3 : x = Digit.three
    · subst h3
      have e : (parentsAt (u ++ [Digit.three])).even = (parentsAt u).current .even := by
        rw [CeilWords.parentsAt_snoc_three]
      refine TileHalfTurnCorr.halfTurn_altEven_corr D f _ u1 u2 hr hl1 hl2 (by simp) aev rAE cAE hP hQ ?_ ?_ (y0 _ sAE)
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossEven D hS hA hspec f u hGu (hnotb3 rfl) true true
      · rw [edl, JointRot.below_of_lt f _ u hul, e]
        exact crossEven D hS hA hspec f u hGu (hnotb3 rfl) false true
    · have hu1 : u1 = u := by
        have h := ConnectedAltL.regs_pre_fst u x h3
        rw [hr] at h
        exact Option.some.inj h
      subst hu1
      exact TileHalfTurnAlt.halfTurn_altEven D f u1 x h3 u2 (by rw [hr]) hl2 aev rAE cAE hP hQ hH.2.2.1 (y0 _ sAE)

end FLatticePaper.Tiles.TileHalfTurnInput
