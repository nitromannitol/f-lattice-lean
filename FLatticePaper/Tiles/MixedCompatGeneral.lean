import FLatticePaper.Tiles.MixedGradeValues

/-! Local compatibility of the mixed registers in the two standard children. -/

namespace FLatticePaper.Tiles.MixedCompatGeneral

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard StandardClause SiteStrings SiteInduction SurgicalWeak JointFamily JointInduction JointRot
open MixedPieces ChildGlue ClosedPathAssembly ClosedPathCycle ClosedPathSum MixedOverlapStrings
open MixedCompatEdges MixedCompatWalks MixedStringGrade

private abbrev XO (u : Word) := texV1Odd (fracOdd u)
private abbrev XE (v : Word) := texV1Even (fracEven v)
private abbrev D (X Y : Site) := X+Y+((1,-1) : Site)
private abbrev cut (X z : Site) := rotR (z-(X-((0,1) : Site)))

private def oddStrip (u : Word) (z : Site) := z ∈ oddTile u ∧ -(fracOdd u).num < tCo (fracOdd u) z
private def evenStrip (v : Word) (z : Site) := z ∈ evenTile v ∧ -(fracEven v).num < tCo (fracEven v) z

private abbrev OS (u : Word) := onSide (oddStrip u) (evenStrip (swapW u)) (XO u) (texV2 (fracOdd u))
private abbrev ES (v : Word) := onSide (evenStrip v) (oddStrip (swapW v)) (XE v) (texV2 (fracEven v))

private theorem half_odd (u : Word) (z : Site) (hz : z ∈ oddTile u) :
    D (XO u) (texV2 (fracOdd u))-z ∈ oddTile u := by
  have h := MarksIn.halfTurn_oddTile u z hz
  have eq : halfTurn (oddTile u) z = D (XO u) (texV2 (fracOdd u))-z := by
    simp only [halfTurn, SiteHullOdd.centre_odd, curO, XO, fracOdd, texV1Odd,texV2,Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    exact ⟨by ring, by ring⟩
  rwa [eq] at h

private theorem half_even (v : Word) (z : Site) (hz : z ∈ evenTile v) :
    D (XE v) (texV2 (fracEven v))-z ∈ evenTile v := by
  have h := MarksIn.halfTurn_evenTile v z hz
  have eq : halfTurn (evenTile v) z = D (XE v) (texV2 (fracEven v))-z := by
    simp only [halfTurn, SiteHullEven.centre_even, curE, XE, fracEven, texV1Even,texV2,Prod.ext_iff,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    exact ⟨by ring, by ring⟩
  rwa [eq] at h

private theorem invert_tile (P Q : Tile) (X z : Site) (h : rot Q = shift P (- (X-((0,1) : Site)))) (hz : z ∈ P) :
    cut X z ∈ Q := by
  apply Standard.mem_rot.mp
  rw [h, Standard.mem_shift, sub_neg_eq_add, sub_add_cancel]
  exact hz

private theorem turn_odd (u : Word) (z : Site) (hz : z ∈ oddTile u) :
    cut (XO u) z ∈ evenTile (swapW u) := by
  apply invert_tile (oddTile u) _ _ z _ hz
  rw [(rot_standard_tiles (swapW u)).2, swapW_swapW', SiteHullOdd.curE_swapW,
      Fraction.rotate_of_odd (SiteHullOdd.curO_odd u)]
  congr 1
  ext <;> simp [tF,tV,curO,XO,fracOdd,texV1Odd] <;> ring

private theorem turn_even (v : Word) (z : Site) (hz : z ∈ evenTile v) :
    cut (XE v) z ∈ oddTile (swapW v) := by
  apply invert_tile (evenTile v) _ _ z _ hz
  have hrot : (parentsAt (swapW v)).current .odd = (curE v).rotate := by
    rw [parentsAt_swapW]; exact ((parentsAt_valid v).rotate_current_even).symm
  rw [(rot_standard_tiles (swapW v)).1, swapW_swapW', hrot, Fraction.rotate_of_even (SiteHullEven.curE_even v)]
  have ev := SiteHullEven.curE_num_add_den_even v
  change ((fracEven v).num+(fracEven v).den)%2 = 0 at ev
  congr 1
  ext <;> simp [tF,tV,show curE v = fracEven v from rfl,XE,texV1Even] <;> omega

private def offsetSum (w : Word) (p q : Site) : Side → Prop
  | .hPlus => contactSum w (D (vQ1 w) (vQ2 w)+q-p)
  | .hMinus => contactSum w (D (vP1 w) (vP2 w)+p-q)
  | .vPlus => contactSum (swapW w) (rotR (q-p+vQ2 w-vP1 w+(1,1)))
  | .vMinus => contactSum (swapW w) (rotR (p-q+vP2 w-vQ1 w+(1,1)))

private theorem cut_inv (X z : Site) : mulI (cut X z) + (X-((0,1) : Site)) = z := by
  ext <;> simp [cut,mulI,rotR]

private theorem two_sides (w u v : Word) (hw : ¬ IsBase w.dropLast) (hr : regsAt w = (some u,some v))
    (p q z : Site) (s : Side) (ho : offsetSum w p q s) (hx : z-p ∈ oddTile u) (hy : z-q ∈ evenTile v) :
    OS u s (z-p) ∧ ES v (opposite s) (z-q) := by
  have ru : (regsAt w).1 = some u := by rw [hr]
  have rv : (regsAt w).2 = some v := by rw [hr]
  have hp := (WeakStepAssembly.regsAt_parents w).1 u ru
  have hq := (WeakStepAssembly.regsAt_parents w).2 v rv
  have sw : ¬ IsBase (swapW w).dropLast := by
    rw [dropLast_swapW]; intro h; apply hw; simpa only [swapW_swapW'] using isBase_swapW h
  have rr : regsAt (swapW w) = (some (swapW v),some (swapW u)) := by rw [regsAt_swapW,hr]; rfl
  have hpr := (WeakStepAssembly.regsAt_parents (swapW w)).1 (swapW v) (by rw [rr])
  have hqr := (WeakStepAssembly.regsAt_parents (swapW w)).2 (swapW u) (by rw [rr])
  have H (x y : Site) (hx' : x ∈ oddTile u) (hy' : y ∈ evenTile v) (hc : contactSum w (x+y)) :
      oddStrip u x ∧ evenStrip v y :=
    let h := contact_grades w u v hw hp hq x y hx' hy' hc
    ⟨⟨hx',h.1⟩,⟨hy',h.2⟩⟩
  have R (x y : Site) (hx' : x ∈ evenTile (swapW u)) (hy' : y ∈ oddTile (swapW v))
      (hc : contactSum (swapW w) (y+x)) : evenStrip (swapW u) x ∧ oddStrip (swapW v) y :=
    let h := contact_grades _ _ _ sw hpr hqr y x hy' hx' hc
    ⟨⟨hx',h.2⟩,⟨hy',h.1⟩⟩
  cases s with
  | hPlus =>
    apply H _ _ hx (half_even v _ hy)
    change contactSum w (D (vQ1 w) (vQ2 w)+q-p) at ho
    simp only [vQ1,vQ2,hq] at ho
    convert ho using 1; abel
  | hMinus =>
    apply H _ _ (half_odd u _ hx) hy
    change contactSum w (D (vP1 w) (vP2 w)+p-q) at ho
    simp only [vP1,vP2,hp] at ho
    convert ho using 1; abel
  | vPlus =>
    let x := z-p
    let y := D (XE v) (texV2 (fracEven v))-(z-q)
    have hr' := R _ _ (turn_odd u x hx) (turn_even v y (half_even v _ hy))
    have h : contactSum (swapW w) (cut (XE v) y + cut (XO u) x) := by
      change contactSum (swapW w) (rotR (q-p+vQ2 w-vP1 w+(1,1))) at ho
      simp only [vQ2,vP1,hp,hq] at ho
      convert ho using 1
      ext <;> simp [x,y,D,cut,rotR] <;> ring
    exact ⟨⟨_,(hr' h).1,(cut_inv _ _).symm⟩,⟨_,(hr' h).2,(cut_inv _ _).symm⟩⟩
  | vMinus =>
    let x := D (XO u) (texV2 (fracOdd u))-(z-p)
    let y := z-q
    have hr' := R _ _ (turn_odd u x (half_odd u _ hx)) (turn_even v y hy)
    have h : contactSum (swapW w) (cut (XE v) y + cut (XO u) x) := by
      change contactSum (swapW w) (rotR (p-q+vP2 w-vQ1 w+(1,1))) at ho
      simp only [vP2,vQ1,hp,hq] at ho
      convert ho using 1
      ext <;> simp [x,y,D,cut,rotR] <;> ring
    exact ⟨⟨_,(hr' h).1,(cut_inv _ _).symm⟩,⟨_,(hr' h).2,(cut_inv _ _).symm⟩⟩

private abbrev so (w : Word) (i j : ℕ) := stringSide (chooseOdd (phase w == 1) i j).1
private abbrev se (w : Word) (i j : ℕ) := stringSide (chooseEven (phase w == 1) i j).1

set_option hygiene false in
local macro "contact_table" : tactic => `(tactic| (
  have rotA : texV1Odd (parentsAt (swapW w)).odd = _ := (vecs_swapW w).1
  have rotU : texV1Even (parentsAt (swapW w)).even = _ := (vecs_swapW w).2.2.1
  have ra₁ := congrArg Prod.fst rotA
  have ra₂ := congrArg Prod.snd rotA
  have ru₁ := congrArg Prod.fst rotU
  have ru₂ := congrArg Prod.snd rotU
  simp only [texV1Odd,texV1Even] at ra₁ ra₂ ru₁ ru₂
  by_cases h : phase w = 1
  all_goals try simp only [ClosedPathStandard.ExclOdd, h, if_true, if_false] at ex
  all_goals fin_cases i <;> fin_cases j <;> first
    | exact Or.inr ex.1
    | exact Or.inr ex.2
    | left; simp [so, se, chooseOdd, chooseEven, stringSide, h, oddP, oddQ, evenP, evenQ,
        pOffsetsOdd, qOffsetsOdd, pOffsetsEven, qOffsetsEven, offsetSum, contactSum, D, Standard.phase_swapW,
        rotA,rotU,vP1,vQ1,vP2,vQ2,texV1Odd,texV1Even,texV2,rotR,Prod.ext_iff] <;> omega))

private theorem table_odd (w u v : Word) (hp : (parentsAt w).odd = fracOdd u)
    (hq : (parentsAt w).even = fracEven v) (i : Fin 2) (j : Fin 4) :
    offsetSum w ((oddP w).getD i 0) ((oddQ w).getD j 0) (so w i j) ∨
      ∀ z, z ∈ dOdd w u v i → z ∈ dOdd w u v (j+2 : ℕ) → False := by
  have ex := ClosedPathDiagonal.exclOdd_all w u v hp hq
  contact_table

private theorem table_even (w u v : Word) (hp : (parentsAt w).odd = fracOdd u)
    (hq : (parentsAt w).even = fracEven v) (i : Fin 4) (j : Fin 2) :
    offsetSum w ((evenP w).getD i 0) ((evenQ w).getD j 0) (se w i j) ∨
      ∀ z, z ∈ dEven w u v i → z ∈ dEven w u v (j+4 : ℕ) → False := by
  have ex := ClosedPathDiagonal.exclEven_all w u v hp hq
  contact_table

private theorem sides (w u v : Word) (hw : ¬ IsBase w.dropLast) (hr : regsAt w = (some u,some v)) :
    OnParentSides w u v (OS u) (ES v) := by
  have hp := (WeakStepAssembly.regsAt_parents w).1 u (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 v (by rw [hr])
  constructor
  · intro i j z hz hy
    have P := mOdd_sub _ _ _ _ hz
    have Q := mOdd_sub _ _ _ _ hy
    rcases table_odd w u v hp hq i j with sum | ex
    · apply two_sides w u v hw hr _ _ z _ sum
      · apply sub_mem_of_shift (tOddSet u)
        simpa only [dOdd,pieceSet,oddP_length,if_pos i.isLt] using P
      · apply sub_mem_of_shift (tEvenSet v)
        simpa only [dOdd,pieceSet,oddP_length,if_neg (by omega : ¬ j.val+2 < 2),Nat.add_sub_cancel] using Q
    · exact (ex z P Q).elim
  · intro i j z hz hy
    have P := mEven_sub _ _ _ _ hz
    have Q := mEven_sub _ _ _ _ hy
    rcases table_even w u v hp hq i j with sum | ex
    · apply two_sides w u v hw hr _ _ z _ sum
      · apply sub_mem_of_shift (tOddSet u)
        simpa only [dEven,pieceSet,evenP_length,if_pos i.isLt] using P
      · apply sub_mem_of_shift (tEvenSet v)
        simpa only [dEven,pieceSet,evenP_length,if_neg (by omega : ¬ j.val+4 < 4),Nat.add_sub_cancel] using Q
    · exact (ex z P Q).elim

private theorem traces (J : JointData) (f : Word → JSlice) (w u v : Word)
    (hS : J.S = WeakStepPaper.paperS) (hA : J.altBase = SurgicalAlt.PaperAltBaseCond)
    (hg : GoodBelow J f w.length) (hr : regsAt w = (some u,some v)) :
    SideTraces (f u).tOdd (XO u) ((fracOdd u).num,-(fracOdd u).den) (OS u) ∧
    SideTraces (f v).tEven (XE v) ((fracEven v).num,-(fracEven v).den) (ES v) := by
  have lu := regsAt_lt w u (Or.inl (by rw [hr]))
  have lv := regsAt_lt w v (Or.inr (by rw [hr]))
  have ls (k : Word) (hk : k.length < w.length) : (swapW k).length < w.length := by
    rwa [length_swapW]
  have sl (k : Word) (hk : k.length < w.length) := family_slopes J f k.length
    (fun l hl => (hg l (lt_of_le_of_lt hl hk)).1) (baseSlopes_paper J hS hA) k le_rfl
  have r (k : Word) (hk : k.length < w.length) := WeakStepAssembly.slice_respects J f k (hg k hk).1
  have dom (k : Word) (hk : k.length < w.length) :
      (f k).tOdd.dom = oddTile k ∧ (f k).tEven.dom = evenTile k := by
    have h := WeakStepAssembly.slice_domains J f k (hg k hk).1
    rw [hS] at h; exact h
  constructor
  · obtain ⟨β,hβ⟩ := (sl u lu).1
    obtain ⟨γ,hγ⟩ := (sl (swapW u) (ls u lu)).2.1
    intro s
    exact four_traces _ _ _ _ _ _ _ β γ hβ hγ
      (fun z h => MixedGradeValues.odd_value u _ β (r u lu).1.2.1 hβ z h.1 h.2)
      (fun z h => MixedGradeValues.even_value (swapW u) _ γ (r _ (ls u lu)).2.2.1 hγ z h.1 h.2)
      (fun _ h => (dom _ (ls u lu)).2.symm ▸ h.1) (hg u lu).2.2.1.2.2.1 (hg u lu).2.2.2.1.1 s
  · obtain ⟨β,hβ⟩ := (sl v lv).2.1
    obtain ⟨γ,hγ⟩ := (sl (swapW v) (ls v lv)).1
    intro s
    exact four_traces _ _ _ _ _ _ _ β γ hβ hγ
      (fun z h => MixedGradeValues.even_value v _ β (r v lv).2.2.1 hβ z h.1 h.2)
      (fun z h => MixedGradeValues.odd_value (swapW v) _ γ (r _ (ls v lv)).1.2.1 hγ z h.1 h.2)
      (fun _ h => (dom _ (ls v lv)).1.symm ▸ h.1) (hg v lv).2.2.1.2.2.2.1 (hg v lv).2.2.2.1.2.1 s

/-- Both standard children have compatible mixed copies for every non-base predecessor. -/
theorem mixed (J : JointData) (f : Word → JSlice) (w u v : Word)
    (hS : J.S = WeakStepPaper.paperS) (hA : J.altBase = SurgicalAlt.PaperAltBaseCond)
    (hg : GoodBelow J f w.length) (hr : regsAt w = (some u,some v)) (hw : ¬ IsBase w.dropLast) :
    MixedCompatOdd w u v (placedOdd w (f u).tOdd.val (f v).tEven.val 0) ∧
    MixedCompatEven w u v (placedEven w (f u).tOdd.val (f v).tEven.val 0) := by
  obtain ⟨to',te⟩ := traces J f w u v hS hA hg hr
  apply mixed_of_traces J f w u v hS hg hr (OS u) (ES v) _ _ (sides w u v hw hr)
  · change SideTraces _ (texV1Odd (parentsAt w).odd) ((parentsAt w).odd.num,-(parentsAt w).odd.den) _
    simpa only [(WeakStepAssembly.regsAt_parents w).1 u (by rw [hr])] using to'
  · change SideTraces _ (texV1Even (parentsAt w).even) ((parentsAt w).even.num,-(parentsAt w).even.den) _
    simpa only [(WeakStepAssembly.regsAt_parents w).2 v (by rw [hr])] using te

/-- The mixed compatibility input of the weak standard step for the paper base data. -/
theorem mixedCompatInput (J : JointData) (hS : J.S = WeakStepPaper.paperS)
    (hA : J.altBase = SurgicalAlt.PaperAltBaseCond) : WeakStepAssembly.MixedCompatInput J := by
  apply MixedCompatBaseStep.mixedCompatInput_of_nonbase_prefix J hS
  intro f w u v hg _ hr hw
  exact mixed J f w u v hS hA hg hr hw

/-- All mixed comparisons among the six standard entries of either alternate child. -/
theorem alt_mixed (J : JointData) (hS : J.S = WeakStepPaper.paperS)
    (hA : J.altBase = SurgicalAlt.PaperAltBaseCond) (f : Word → JSlice) (w u v : Word)
    (hg : GoodBelow J f w.length) (hw : ¬ IsBase w) (hr : regsAt w = (some u,some v)) (c : ℕ → ℤ) :
    ClosedPathAlt.AltMixedCompatOdd w u v (ClosedPathAlt.placedAltOdd w (f u).tOdd.val (f v).tEven.val c) ∧
    ClosedPathAlt.AltMixedCompatEven w u v (ClosedPathAlt.placedAltEven w (f u).tOdd.val (f v).tEven.val c) := by
  have h := (mixedCompatInput J hS hA f w u v hg hw hr).1
  have hp := (WeakStepAssembly.regsAt_parents w).1 u (by rw [hr])
  have hq := (WeakStepAssembly.regsAt_parents w).2 v (by rw [hr])
  exact ⟨AltMixedCompat.odd_of_standard _ _ _ hp hq _ _ c h, AltMixedCompat.even_of_standard _ _ _ hp hq _ _ c h⟩

end FLatticePaper.Tiles.MixedCompatGeneral
