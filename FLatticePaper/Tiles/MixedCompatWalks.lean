import FLatticePaper.Tiles.MixedCompatEdges
import FLatticePaper.Tiles.MixedCompatBaseStep
import FLatticePaper.Tiles.MixedOverlapStrings

/-! The local height comparison at a mixed pair follows from the locations of
its shared vertices on the boundary walks of its two parents. -/

namespace FLatticePaper.Tiles.MixedCompatWalks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open StandardClause Standard SurgicalWeak SiteStrings JointFamily JointInduction MixedCompatEdges
open ClosedPathAssembly ClosedPathCycle ClosedPathSum ChildGlue MixedPieces MixedOverlapStrings

/-- The facing side of the other parent. -/
def opposite : Side → Side
  | .hPlus => .hMinus
  | .hMinus => .hPlus
  | .vPlus => .vMinus
  | .vMinus => .vPlus

/-- The four indices in the order of the marked strings. -/
def stringSide (i : Fin 4) : Side :=
  if i = 0 then .hPlus else if i = 1 then .vMinus else if i = 2 then .hMinus else .vPlus

private def fits (X U a b p q s t : Site) : Side → Prop
  | .hPlus => s = t + b
  | .hMinus => t = s + a
  | .vPlus => EvenSite (q-(p+X)) ∧ t = s + JointRot.hHalf (q-(p+X))
  | .vMinus => EvenSite ((q+U)-p) ∧ t = s + JointRot.hHalf ((q+U)-p)

private theorem vertical (p q s t : Site) (he : EvenSite (q-p))
    (ht : t = s + JointRot.hHalf (q-p)) :
    ∃ C : ℤ, ∀ z, -h0 (z-p) + dotS s z - (-h0 (z-q) + dotS t z) = C := by
  refine ⟨centeredQuarterTurnCorrection (q-p) - dotS (JointRot.hHalf (q-p)) q, fun z => ?_⟩
  have H := JointRot.h0_sub (z-p) (q-p) he
  rw [show z-p-(q-p) = z-q by abel] at H
  rw [ht]
  simp only [dotS, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at H ⊢
  linear_combination -H

private theorem height_difference (X U a b p q s t : Site) (side : Side) (fit : fits X U a b p q s t side) :
    ∃ C : ℤ, ∀ z, edgeHeight X a side (z-p) + dotS s z -
      (edgeHeight U b (opposite side) (z-q) + dotS t z) = C := by
  cases side with
  | hPlus =>
    refine ⟨dotS b q, fun z => ?_⟩
    change s = t + b at fit
    simp [edgeHeight, opposite, fit, dotS]; ring
  | hMinus =>
    refine ⟨-dotS a p, fun z => ?_⟩
    change t = s + a at fit
    simp [edgeHeight, opposite, fit, dotS]; ring
  | vPlus =>
    have H := vertical (p+X) q s t fit.1 fit.2
    simpa only [edgeHeight, opposite, sub_sub] using H
  | vMinus =>
    have H := vertical p (q+U) s t fit.1 fit.2
    simpa only [edgeHeight, opposite, sub_sub] using H

private abbrev A (w : Word) := texV1Odd (parentsAt w).odd
private abbrev U (w : Word) := texV1Even (parentsAt w).even
private abbrev ap (w : Word) : Site := ((parentsAt w).odd.num,-(parentsAt w).odd.den)
private abbrev aq (w : Word) : Site := ((parentsAt w).even.num,-(parentsAt w).even.den)

private abbrev sideO (w : Word) (i j : ℕ) := stringSide (chooseOdd (phase w == 1) i j).1
private abbrev sideE (w : Word) (i j : ℕ) := stringSide (chooseEven (phase w == 1) i j).1

private abbrev fitO (w : Word) (i j : ℕ) := fits (A w) (U w) (ap w) (aq w)
  ((oddP w).getD i 0) ((oddQ w).getD j 0) (affOdd (parentsAt w).odd (parentsAt w).even i)
  (affOdd (parentsAt w).odd (parentsAt w).even (j+2)) (sideO w i j)

private abbrev fitE (w : Word) (i j : ℕ) := fits (A w) (U w) (ap w) (aq w)
  ((evenP w).getD i 0) ((evenQ w).getD j 0) (affEven (parentsAt w).odd (parentsAt w).even i)
  (affEven (parentsAt w).odd (parentsAt w).even (j+4)) (sideE w i j)

private theorem odd_table (w u v : Word) (hp : (parentsAt w).odd = fracOdd u) (hq : (parentsAt w).even = fracEven v)
    (i : Fin 2) (j : Fin 4) : fitO w i j ∨ ∀ z, z ∈ dOdd w u v i → z ∈ dOdd w u v (j+2 : ℕ) → False := by
  have ex := ClosedPathDiagonal.exclOdd_all w u v hp hq
  by_cases h : phase w = 1
  all_goals simp only [ClosedPathStandard.ExclOdd, h, if_true, if_false] at ex
  all_goals fin_cases i <;> fin_cases j <;> first
    | exact Or.inr ex.1
    | exact Or.inr ex.2
    | left; simp [fitO, fits, A, U, oddP, oddQ, pOffsetsOdd, qOffsetsOdd, affOdd, sideO, chooseOdd, stringSide, h,
        texV1Odd, texV1Even, texV2, ap, aq, EvenSite, JointRot.hHalf, Prod.ext_iff] <;> omega

private theorem even_table (w u v : Word) (hp : (parentsAt w).odd = fracOdd u) (hq : (parentsAt w).even = fracEven v)
    (i : Fin 4) (j : Fin 2) : fitE w i j ∨ ∀ z, z ∈ dEven w u v i → z ∈ dEven w u v (j+4 : ℕ) → False := by
  have ex := ClosedPathDiagonal.exclEven_all w u v hp hq
  by_cases h : phase w = 1
  all_goals fin_cases i <;> fin_cases j <;> first
    | exact Or.inr ex.1
    | exact Or.inr ex.2
    | left; simp [fitE, fits, A, U, evenP, evenQ, pOffsetsEven, qOffsetsEven, affEven, sideE, chooseEven, stringSide, h,
        texV1Odd, texV1Even, texV2, ap, aq, EvenSite, JointRot.hHalf, Prod.ext_iff] <;> omega

/-- A placed point is on the indicated walk of the odd parent and the opposite walk of the even parent. -/
def parentWalkPair (w u v : Word) (p q : Site) (s : Side) (z : Site) : Prop :=
  edge (hWordOf u false) (hWordOf (swapW u) true) (A w) (texV2 (parentsAt w).odd) s (z-p) ∧
  edge (hWordOf v true) (hWordOf (swapW v) false) (U w) (texV2 (parentsAt w).even) (opposite s) (z-q)

/-- The geometric conclusion on the two parents' boundary walks at a non-base prefix.
The indices for the even register start at zero in its list of offsets. -/
def OnParentWalks (w u v : Word) : Prop :=
  (∀ (i : Fin 2) (j : Fin 4) (z : Site), z ∈ mOdd w u v i → z ∈ mOdd w u v (j+2 : ℕ) →
    parentWalkPair w u v ((oddP w).getD i 0) ((oddQ w).getD j 0) (sideO w i j) z) ∧
  (∀ (i : Fin 4) (j : Fin 2) (z : Site), z ∈ mEven w u v i → z ∈ mEven w u v (j+4 : ℕ) →
    parentWalkPair w u v ((evenP w).getD i 0) ((evenQ w).getD j 0) (sideE w i j) z)

/-- The intersection of the two selected strings is on their boundary walks.
All the sets in this condition come from the two boundary words. -/
def SelectedStringWalks (w u v : Word) : Prop :=
  (∀ (i : Fin 2) (j : Fin 4) (z : Site),
    let ks := chooseOdd (phase w == 1) i j
    z - (oddP w).getD i 0 ∈ oddStr u ks.1 → z - (oddQ w).getD j 0 ∈ evenStr v ks.2 →
    parentWalkPair w u v ((oddP w).getD i 0) ((oddQ w).getD j 0) (stringSide ks.1) z) ∧
  (∀ (i : Fin 4) (j : Fin 2) (z : Site),
    let ks := chooseEven (phase w == 1) i j
    z - (evenP w).getD i 0 ∈ oddStr u ks.1 → z - (evenQ w).getD j 0 ∈ evenStr v ks.2 →
    parentWalkPair w u v ((evenP w).getD i 0) ((evenQ w).getD j 0) (stringSide ks.1) z)

/-- Apply the packing statements to the actual registers, then restrict to the two selected strings. -/
theorem walks_of_selected (w u v : Word) (hr : regsAt w = (some u, some v))
    (ho : OverlapInStringsOdd w) (he : OverlapInStringsEven w) (hs : SelectedStringWalks w u v) :
    OnParentWalks w u v := by
  have hu := (WeakStepPaper.regsAt_tiles w).1 u (by rw [hr])
  have hv := (WeakStepPaper.regsAt_tiles w).2.2.1 v (by rw [hr])
  constructor
  · intro i j z h₁ h₂
    have hP := mOdd_sub w u v i h₁
    have hQ := mOdd_sub w u v (j.val+2) h₂
    have hi := i.isLt
    simp only [dOdd, pieceSet, oddP_length, if_pos hi, if_neg (by omega : ¬ j.val+2 < 2),
      Nat.add_sub_cancel] at hP hQ
    obtain ⟨h, k⟩ := ho u v hu hv i j (by rw [oddP_length]; exact i.isLt) (by rw [oddQ_length]; exact j.isLt) z hP hQ
    exact hs.1 i j z (sub_mem_of_shift _ _ _ h) (sub_mem_of_shift _ _ _ k)
  · intro i j z h₁ h₂
    have hP := mEven_sub w u v i h₁
    have hQ := mEven_sub w u v (j.val+4) h₂
    have hi := i.isLt
    simp only [dEven, pieceSet, evenP_length, if_pos hi, if_neg (by omega : ¬ j.val+4 < 4),
      Nat.add_sub_cancel] at hP hQ
    obtain ⟨h, k⟩ := he u v hu hv i j (by rw [evenP_length]; exact i.isLt) (by rw [evenQ_length]; exact j.isLt) z hP hQ
    exact hs.2 i j z (sub_mem_of_shift _ _ _ h) (sub_mem_of_shift _ _ _ k)

private def traceOn (w u : Word) (par : Bool) (o : PartialOdometer) : Prop :=
  let r := if par then (parentsAt w).even else (parentsAt w).odd
  let X := if par then U w else A w
  ∀ s : Side, ∃ k : ℤ, ∀ z ∈ o.dom, edge (hWordOf u par) (hWordOf (swapW u) (!par)) X (texV2 r) s z →
      o.val z - edgeHeight X (r.num, -r.den) s z = k

private theorem parent_traces (D : JointData) (f : Word → JSlice) (w u v : Word)
    (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hg : GoodBelow D f w.length) (hr : regsAt w = (some u, some v)) :
    traceOn w u false (f u).tOdd ∧ traceOn w v true (f v).tEven := by
  have ru : (regsAt w).1 = some u := by rw [hr]
  have rv : (regsAt w).2 = some v := by rw [hr]
  have hu := regsAt_lt w u (Or.inl ru)
  have hv := regsAt_lt w v (Or.inr rv)
  have hru : (swapW u).length < w.length := by rwa [JointRot.length_swapW]
  have hrv : (swapW v).length < w.length := by rwa [JointRot.length_swapW]
  have sl (k : Word) (hk : k.length < w.length) :=
    JointRot.family_slopes D f k.length (fun l hl => (hg l (lt_of_le_of_lt hl hk)).1)
      (JointRot.baseSlopes_paper D hS hA) k le_rfl
  have res (k : Word) (hk : k.length < w.length) := WeakStepAssembly.slice_respects D f k (hg k hk).1
  have hp := (WeakStepAssembly.regsAt_parents w).1 u ru
  have hq := (WeakStepAssembly.regsAt_parents w).2 v rv
  constructor
  · intro side
    simp only [Bool.false_eq_true, if_false, Bool.not_false, A, hp] at *
    exact four_edges _ _ _ _ _ _ _ _ _
      (hWordOf_head_last u false).1 (hWordOf_head_last u false).2
      (hWordOf_head_last (swapW u) true).1 (hWordOf_head_last (swapW u) true).2
      (res u hu).1 (res (swapW u) hru).2 (sl u hu).1 (sl (swapW u) hru).2.1
      (hg u hu).2.2.1.2.2.1 (hg u hu).2.2.2.1.1 side
  · intro side
    simp only [if_true, Bool.not_true, U, hq] at *
    exact four_edges _ _ _ _ _ _ _ _ _
      (hWordOf_head_last v true).1 (hWordOf_head_last v true).2
      (hWordOf_head_last (swapW v) false).1 (hWordOf_head_last (swapW v) false).2
      (res v hv).2 (res (swapW v) hrv).1 (sl v hv).2.1 (sl (swapW v) hrv).1
      (hg v hv).2.2.1.2.2.2.1 (hg v hv).2.2.2.1.2.1 side

/-- The affine formula on the chosen sites of each side of an odometer. -/
def SideTraces (P : PartialOdometer) (X a : Site) (F : Side → Site → Prop) : Prop :=
  ∀ s, ∃ k : ℤ, ∀ z ∈ P.dom, F s z → P.val z - edgeHeight X a s z = k

private theorem pair (w : Word) (P Q : PartialOdometer) (F G : Side → Site → Prop)
    (hp : SideTraces P (A w) (ap w) F) (hq : SideTraces Q (U w) (aq w) G)
    (p q s t : Site) (side : Side) (fit : fits (A w) (U w) (ap w) (aq w) p q s t side) :
    ∃ C : ℤ, ∀ z, z-p ∈ P.dom → z-q ∈ Q.dom → F side (z-p) ∧ G (opposite side) (z-q) →
      P.val (z-p) + dotS s z - (Q.val (z-q) + dotS t z) = C := by
  obtain ⟨C, hC⟩ := height_difference _ _ _ _ _ _ _ _ _ fit
  obtain ⟨K, hK⟩ := hp side
  obtain ⟨L, hL⟩ := hq (opposite side)
  refine ⟨K - L + C, fun z hP hQ he => ?_⟩
  have eP := hK _ hP he.1
  have eQ := hL _ hQ he.2
  change P.val (z-p) - edgeHeight (A w) (ap w) side (z-p) = K at eP
  change Q.val (z-q) - edgeHeight (U w) (aq w) (opposite side) (z-q) = L at eQ
  linarith only [eP,eQ,hC z]

/-- The common marks lie in the chosen side sets of their two parents. -/
def OnParentSides (w u v : Word) (F G : Side → Site → Prop) : Prop :=
  (∀ (i : Fin 2) (j : Fin 4) (z : Site), z ∈ mOdd w u v i → z ∈ mOdd w u v (j+2 : ℕ) →
    F (sideO w i j) (z-(oddP w).getD i 0) ∧ G (opposite (sideO w i j)) (z-(oddQ w).getD j 0)) ∧
  (∀ (i : Fin 4) (j : Fin 2) (z : Site), z ∈ mEven w u v i → z ∈ mEven w u v (j+4 : ℕ) →
    F (sideE w i j) (z-(evenP w).getD i 0) ∧ G (opposite (sideE w i j)) (z-(evenQ w).getD j 0))

/-- Mixed compatibility from two normalized side traces and the locations of the common sites. -/
theorem mixed_of_traces (D : JointData) (f : Word → JSlice) (w u v : Word)
    (hS : D.S = WeakStepPaper.paperS) (hg : GoodBelow D f w.length) (hr : regsAt w = (some u, some v))
    (F G : Side → Site → Prop) (tP : SideTraces (f u).tOdd (A w) (ap w) F)
    (tQ : SideTraces (f v).tEven (U w) (aq w) G) (sides : OnParentSides w u v F G) :
    MixedCompatOdd w u v (placedOdd w (f u).tOdd.val (f v).tEven.val 0) ∧
    MixedCompatEven w u v (placedEven w (f u).tOdd.val (f v).tEven.val 0) := by
  obtain ⟨gO,gE⟩ := sides
  have ru : (regsAt w).1 = some u := by rw [hr]
  have rv : (regsAt w).2 = some v := by rw [hr]
  have hP := (WeakStepAssembly.regsAt_parents w).1 u ru
  have hQ := (WeakStepAssembly.regsAt_parents w).2 v rv
  have domP : (f u).tOdd.dom = oddTile u := by
    rw [(WeakStepAssembly.slice_domains D f u (hg u (regsAt_lt w u (Or.inl ru))).1).1, hS]; rfl
  have domQ : (f v).tEven.dom = evenTile v := by
    rw [(WeakStepAssembly.slice_domains D f v (hg v (regsAt_lt w v (Or.inr rv))).1).2, hS]; rfl
  constructor
  · intro i j hi hj hj'
    let I : Fin 2 := ⟨i,hi⟩
    let J : Fin 4 := ⟨j-2,by omega⟩
    have ej : (J : ℕ)+2 = j := Nat.sub_add_cancel hj
    rcases odd_table w u v hP hQ I J with fit | ex
    · obtain ⟨K,hK⟩ := pair w _ _ F G tP tQ _ _ _ _ _ fit
      refine ⟨K, fun z hz hz' => ?_⟩
      have hm := gO I J z hz (ej.symm ▸ hz')
      have p := mOdd_sub w u v i hz
      have q := mOdd_sub w u v j hz'
      simp only [dOdd, pieceSet, oddP_length, if_pos hi, if_neg (by omega : ¬ j < 2)] at p q
      have h := hK z (domP.symm ▸ sub_mem_of_shift _ _ _ p) (domQ.symm ▸ sub_mem_of_shift _ _ _ q) hm
      rw [ej] at h
      simpa only [placedOdd, if_pos hi, if_neg (by omega : ¬ j < 2), Pi.zero_apply, add_zero, I, J, dot2, dotS] using h
    · exact ⟨0, fun z hz hz' => (ex z (mOdd_sub _ _ _ _ hz) (ej.symm ▸ mOdd_sub _ _ _ _ hz')).elim⟩
  · intro i j hi hj hj'
    let I : Fin 4 := ⟨i,hi⟩
    let J : Fin 2 := ⟨j-4,by omega⟩
    have ej : (J : ℕ)+4 = j := Nat.sub_add_cancel hj
    rcases even_table w u v hP hQ I J with fit | ex
    · obtain ⟨K,hK⟩ := pair w _ _ F G tP tQ _ _ _ _ _ fit
      refine ⟨K, fun z hz hz' => ?_⟩
      have hm := gE I J z hz (ej.symm ▸ hz')
      have p := mEven_sub w u v i hz
      have q := mEven_sub w u v j hz'
      simp only [dEven, pieceSet, evenP_length, if_pos hi, if_neg (by omega : ¬ j < 4)] at p q
      have h := hK z (domP.symm ▸ sub_mem_of_shift _ _ _ p) (domQ.symm ▸ sub_mem_of_shift _ _ _ q) hm
      rw [ej] at h
      simpa only [placedEven, if_pos hi, if_neg (by omega : ¬ j < 4), Pi.zero_apply, add_zero, I, J, dot2, dotS] using h
    · exact ⟨0, fun z hz hz' => (ex z (mEven_sub _ _ _ _ hz) (ej.symm ▸ mEven_sub _ _ _ _ hz')).elim⟩

/-- Compare the two actual tile odometers on the mixed marks at a given child. -/
theorem mixed_of_walks (D : JointData) (f : Word → JSlice) (w u v : Word)
    (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hg : GoodBelow D f w.length) (hr : regsAt w = (some u, some v)) (walks : OnParentWalks w u v) :
    MixedCompatOdd w u v (placedOdd w (f u).tOdd.val (f v).tEven.val 0) ∧
    MixedCompatEven w u v (placedEven w (f u).tOdd.val (f v).tEven.val 0) := by
  obtain ⟨tP,tQ⟩ := parent_traces D f w u v hS hA hg hr
  exact mixed_of_traces D f w u v hS hg hr _ _ tP tQ walks

/-- The exact local input of the standard step, from the location of the common vertices on the
parent walks at non-base prefixes. Base prefixes include their exceptional end vertices. -/
theorem mixedCompatInput_of_walks (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (walks : ∀ (w u v : Word), ¬ IsBase w.dropLast → regsAt w = (some u, some v) → OnParentWalks w u v) :
    WeakStepAssembly.MixedCompatInput D := by
  apply MixedCompatBaseStep.mixedCompatInput_of_nonbase_prefix D hS
  intro f w u v hg _ hr hn
  exact mixed_of_walks D f w u v hS hA hg hr (walks w u v hn hr)

/-- Mixed compatibility from the two Section 7 packing statements and the positions of the
intersecting selected strings on the boundary walks. Only non-base prefixes need these inputs. -/
theorem mixedCompatInput_of_selected (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (packing : ∀ w : Word, ¬ IsBase w.dropLast → OverlapInStringsOdd w ∧ OverlapInStringsEven w)
    (positions : ∀ w u v : Word, ¬ IsBase w.dropLast → regsAt w = (some u, some v) → SelectedStringWalks w u v) :
    WeakStepAssembly.MixedCompatInput D := by
  apply mixedCompatInput_of_walks D hS hA
  intro w u v hn hr
  exact walks_of_selected w u v hr (packing w hn).1 (packing w hn).2 (positions w u v hn hr)

end FLatticePaper.Tiles.MixedCompatWalks
