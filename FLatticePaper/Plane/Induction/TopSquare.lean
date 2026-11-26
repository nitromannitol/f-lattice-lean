import FLatticePaper.Plane.Induction.PairClass
import FLatticePaper.Plane.Induction.ColourPacket
import FLatticePaper.Plane.Induction.SquareImage
import FLatticePaper.Plane.Induction.CrossingLattice
import FLatticePaper.Plane.Induction.ExteriorNbr
import FLatticePaper.Plane.Induction.BoundarySite
import FLatticePaper.Plane.Induction.BottomExcl
import FLatticePaper.Plane.Induction.Exceptions
import FLatticePaper.Plane.Induction.BottomGrade
import FLatticePaper.Plane.Induction.BottomGradeNeg
import FLatticePaper.Plane.Induction.LeftVWebProof
import FLatticePaper.Plane.Induction.LeftVNegGrade
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.CollarOneOne
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.AndOrRank
import FLatticePaper.Plane.Induction.FanCompat

/-! # The top-square strictness (step (6))

For a strict white centre `c` with a bottom or aligned witness, and a unit square `S` of the conjugate frame whose corners
are strict and whose centre `ρ = zTurn (c − lv) + v` lies in `S`, every corner of the word-image of `S` is strict.
This is the statement `TopStrictHyp` assumes. Its proof: the image square through `c` has a closed non-strict corner `b`
(`crossing_square`); the preimage corner `q'` of `b` is strict, hence `zTurn (b − lv) = q' − v` is nonfree; each type of
closed boundary point `b` (`spectrum_site`) contradicts this, either by a native arc lemma or by a colour exclusion. -/

namespace FLatticePaper.TopSquare

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.W1Phase FLatticePaper.AndOrRank
  FLatticePaper.FanCompat FLatticePaper.FaceWitness FLatticePaper.Induction FLatticePaper.Farey
  FLatticePaper.AlignedClassSite FLatticePaper.BoundaryPair FLatticePaper.StripColours FLatticePaper.W1MSheet
  FLatticePaper.PairClass

/-- Two corners of a unit square are within one pixel in each coordinate. -/
theorem corner_adj (a b : ℤ) {x y : Site} (hx : x ∈ squareCorners a b) (hy : y ∈ squareCorners a b) :
    |x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1 := by
  rw [mem_squareCorners_iff] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor <;> rw [abs_le] <;> constructor <;> omega

/-- The deck span is closed under subtraction. -/
theorem span_sub {frame : FLatticePaper.Induction.ChildFrame} {w v : Site}
    (hw : w ∈ frame.child.modifiedDeck.span) (hv : v ∈ frame.child.modifiedDeck.span) :
    w - v ∈ frame.child.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hw
  obtain ⟨i', j', rfl⟩ := hv
  refine ⟨i - i', j - j', ?_⟩
  simp only [PeriodDeck.combine]
  ext <;> simp <;> ring

/-- A nonfree site stays nonfree after translating by a deck vector. -/
theorem nonfree_sub {frame : FLatticePaper.Induction.ChildFrame} {z v : Site}
    (hz : Nonfree frame z) (hv : v ∈ frame.child.modifiedDeck.span) : Nonfree frame (z - v) := by
  unfold Nonfree at hz ⊢
  intro w hw
  have h := hz (w - v) (span_sub hw hv)
  have e : z - v + w = z + (w - v) := by abel
  rw [e]
  exact h

/-- **No left and right witnesses at a common centre** (for `d ≥ 5`, that is `n ≥ 3`). -/
theorem left_right_excl {n d : ℤ} (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hd5 : 5 ≤ d) {c v w : Site}
    (hvc : |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1) (hwc : |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1)
    (hF : freeVn n d v) (hG : freeVn n d (w.1 - d, w.2 - n)) : False := by
  have hv := hF.2.2
  have hw := hG.2.2
  have eK : w1s n d (w.1 - d, w.2 - n) = w1s n d w - w1T n d := by
    unfold w1s w1T; ring
  rw [eK] at hw
  have hvd : (0 ≤ w1s n d v ∧ w1s n d v ≤ 2 * n) ∨ (2 - d + n ≤ w1s n d v ∧ w1s n d v ≤ d + n - 2) := hv.2
  have hwd : (0 ≤ w1s n d w - w1T n d ∧ w1s n d w - w1T n d ≤ 2 * n) ∨
      (2 - d + n ≤ w1s n d w - w1T n d ∧ w1s n d w - w1T n d ≤ d + n - 2) := hw.2
  have hT6 : 6 * d - 4 < w1T n d := by
    rw [w1T_eq]
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ d - 1) (by omega : (0 : ℤ) ≤ d - 3),
      mul_nonneg (by omega : (0 : ℤ) ≤ n - 1) (by omega : (0 : ℤ) ≤ 2 * d - n - 1)]
  have key : w1s n d w - w1s n d v = (d + n) * (w.1 - v.1) + (d - n) * (w.2 - v.2) := by
    unfold w1s; ring
  obtain ⟨hv1a, hv1b⟩ := abs_le.mp hvc.1
  obtain ⟨hv2a, hv2b⟩ := abs_le.mp hvc.2
  obtain ⟨hw1a, hw1b⟩ := abs_le.mp hwc.1
  obtain ⟨hw2a, hw2b⟩ := abs_le.mp hwc.2
  have dx1 : w.1 - v.1 ≤ 2 := by omega
  have dx2 : -2 ≤ w.1 - v.1 := by omega
  have dy1 : w.2 - v.2 ≤ 2 := by omega
  have dy2 : -2 ≤ w.2 - v.2 := by omega
  have hpn : (0 : ℤ) ≤ d + n := by omega
  have hmn : (0 : ℤ) ≤ d - n := by omega
  have p1 := mul_le_mul_of_nonneg_left dx1 hpn
  have p2 := mul_le_mul_of_nonneg_left dx2 hpn
  have q1 := mul_le_mul_of_nonneg_left dy1 hmn
  have q2 := mul_le_mul_of_nonneg_left dy2 hmn
  have hsv : w1s n d v ≤ d + n - 2 := by rcases hvd with h | h <;> omega
  have hsw : 2 - d + n ≤ w1s n d w - w1T n d := by rcases hwd with h | h <;> omega
  have hdiff : w1s n d w - w1s n d v ≤ 4 * d := by
    rw [key]
    linarith [p1, q1]
  linarith

/-! ## Frame-to-site witnesses -/

theorem leftWit_site {F : FLatticePaper.Induction.ChildFrame} {c : Site} (h : LeftWit F c) :
    ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeVn F.child.num F.child.den v := by
  obtain ⟨v, h1, h2, hv⟩ := h
  exact ⟨v, h1, h2, (freeV_iff_freeVn F v).mp hv⟩

theorem rightWit_site {F : FLatticePaper.Induction.ChildFrame} {c : Site} (h : RightWit F c) :
    ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧
      freeVn F.child.num F.child.den (v.1 - F.child.den, v.2 - F.child.num) := by
  obtain ⟨v, h1, h2, hv⟩ := h
  rw [kernel_eq] at hv
  exact ⟨v, h1, h2, (freeV_iff_freeVn F _).mp hv⟩

theorem bottomWit_site {F : FLatticePaper.Induction.ChildFrame} {c : Site} (h : BottomWit F c) :
    ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeHn F.child.num F.child.den v := by
  obtain ⟨v, h1, h2, hv⟩ := h
  exact ⟨v, h1, h2, (freeH_iff_freeHn F v).mp hv⟩

theorem topWit_site {F : FLatticePaper.Induction.ChildFrame} {c : Site} (h : TopWit F c) :
    ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧
      freeHn F.child.num F.child.den (w.1 - (F.child.num - F.child.den), w.2 - (F.child.num + F.child.den)) := by
  obtain ⟨v, h1, h2, hv⟩ := h
  rw [transverse_eq] at hv
  exact ⟨v, h1, h2, (freeH_iff_freeHn F _).mp hv⟩

/-! ## Corners of a unit square -/

theorem strict_corner_disj {n d a b : ℤ} {x : Site} (hx : x ∈ squareCorners a b)
    (hS : StrictInterior n d x) :
    StrictInterior n d (a, b) ∨ StrictInterior n d (a + 1, b) ∨ StrictInterior n d (a, b + 1) ∨
      StrictInterior n d (a + 1, b + 1) := by
  rw [mem_squareCorners_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; rw [show ((a, b) : Site) = x from Prod.ext h1.symm h2.symm]; exact hS
  · right; right; left; rw [show ((a, b + 1) : Site) = x from Prod.ext h1.symm h2.symm]; exact hS
  · right; left; rw [show ((a + 1, b) : Site) = x from Prod.ext h1.symm h2.symm]; exact hS
  · right; right; right; rw [show ((a + 1, b + 1) : Site) = x from Prod.ext h1.symm h2.symm]; exact hS

theorem all_strict_corner {n d a b : ℤ} {x : Site} (hx : x ∈ squareCorners a b)
    (s0 : StrictInterior n d (a, b)) (s1 : StrictInterior n d (a + 1, b))
    (s2 : StrictInterior n d (a, b + 1)) (s3 : StrictInterior n d (a + 1, b + 1)) :
    StrictInterior n d x := by
  rw [mem_squareCorners_iff] at hx
  obtain ⟨g1, g2⟩ := hx
  rcases g1 with g1 | g1 <;> rcases g2 with g2 | g2
  · rw [show x = (a, b) from Prod.ext g1 g2]; exact s0
  · rw [show x = (a, b + 1) from Prod.ext g1 g2]; exact s2
  · rw [show x = (a + 1, b) from Prod.ext g1 g2]; exact s1
  · rw [show x = (a + 1, b + 1) from Prod.ext g1 g2]; exact s3

theorem corner_mem_all (a b : ℤ) :
    (a, b) ∈ squareCorners a b ∧ (a + 1, b) ∈ squareCorners a b ∧ (a, b + 1) ∈ squareCorners a b ∧
      (a + 1, b + 1) ∈ squareCorners a b := by
  unfold squareCorners
  simp

/-! ## The top-square strictness -/

/-- **The word-image of a conjugate square is strict** (the content of `TopStrictHyp`), for a strict white centre
`c` with a bottom or aligned witness. The colour facts come from the packet (`HasStrips`, `HasGeneratorPeriods`). -/
theorem top_corner_strict (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (c v ρ : Site) (a b : ℤ)
    (hc : StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0)
    (hWit : BottomWit (frameAt word) c ∨ AlignedWit (frameAt word) c)
    (hρ : ρ = zTurn (c - (frameAt word).sheetShift) + v)
    (hv : v ∈ (frameAt (conjWord word)).child.modifiedDeck.span)
    (hsq : ∀ c' ∈ squareCorners a b,
      StrictInterior (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den c')
    (hρS : ρ ∈ squareCorners a b) :
    ∀ q ∈ squareCorners a b, StrictInterior (frameAt word).child.num (frameAt word).child.den
      ((frameAt word).sheetShift + zTurnInv (q - v)) := by
  intro q hq
  by_contra hne
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := (frameAt word).child_facts
  have hn3 := child_num_ge_three hw
  have hn1 : 1 ≤ (frameAt word).child.num := by omega
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by omega
  have hd5 : 5 ≤ (frameAt word).child.den := by omega
  have hTL : 2 * ((frameAt word).child.den + (frameAt word).child.num) <
      w1T (frameAt word).child.num (frameAt word).child.den := by
    have := FLatticePaper.Exceptions.period_ge2 hn1 hnd
    omega
  have hε := (frameAt word).eps_unit
  -- the image square through c
  have hρ' : ρ - v = zTurn (c - (frameAt word).sheetShift) := by rw [hρ]; abel
  have hcS := SquareImage.image_mem a b v (frameAt word).sheetShift ρ hρS
  rw [hρ', zTurnInv_zTurn, sub_add_cancel] at hcS
  have hpS := SquareImage.image_mem a b v (frameAt word).sheetShift q hq
  have hne' : ¬ StrictInterior (frameAt word).child.num (frameAt word).child.den
      (zTurnInv (q - v) + (frameAt word).sheetShift) := by
    rwa [add_comm]
  set A : ℤ := b - v.2 + 1 + (frameAt word).sheetShift.1 with hA
  set B : ℤ := -(a - v.1) - 1 + (frameAt word).sheetShift.2 with hB
  -- crossing: all four strict, or a closed non-strict corner
  have hcr := CrossingLattice.crossing_square hn1 hnd hTL hnO hdO (A, B) (strict_corner_disj hcS hc)
  -- a closed non-strict corner of the image square gives a contradiction
  have key : ∀ bb : Site, bb ∈ squareCorners A B → closedRect (frameAt word).child.num (frameAt word).child.den bb →
      ¬ StrictInterior (frameAt word).child.num (frameAt word).child.den bb → False := by
    intro bb hbbS hcl hns
    obtain ⟨q', hq'mem, hq'eq⟩ := SquareImage.image_preimage a b v (frameAt word).sheetShift bb hbbS
    have e : zTurn (bb - (frameAt word).sheetShift) = q' - v := by
      rw [← hq'eq, add_sub_cancel_right, zTurn_zTurnInv]
    have hq'S := hsq q' hq'mem
    have hNF : Nonfree (frameAt (conjWord word)) (zTurn (bb - (frameAt word).sheetShift)) := by
      rw [e]
      exact nonfree_sub (strictInterior_nonfree _ hq'S) hv
    obtain ⟨ha1, ha2⟩ := corner_adj A B hbbS hcS
    have hX := ExteriorNbr.exterior_nbr hnO hdO hn1 bb hns
    have hspec := BoundarySite.spectrum_site hnO hdO hn1 hnd hTL bb hcl hX
    rcases hε with hε1 | hεm
    · -- the eps = +1 cases
      rcases hspec with hBH | hBV | hKV | hTV
      · by_cases hbl : bb = (frameAt word).hLast
        · have hb1 : bb.1 = (frameAt word).child.den := congrArg Prod.fst hbl
          have hb2 : bb.2 = (frameAt word).child.num - 1 := congrArg Prod.snd hbl
          have hc1 : |c.1 - (frameAt word).child.den| ≤ 1 := by
            rw [abs_le] at ha1 ⊢; constructor <;> omega
          have hc2 : |c.2 - ((frameAt word).child.num - 1)| ≤ 1 := by
            rw [abs_le] at ha2 ⊢; constructor <;> omega
          have hcE := FLatticePaper.Exceptions.hLast_strict hnO hdO hn1 hnd c hc1 hc2 hc
          have hl := ColourPacket.lap_MW_dn1 hw hSE
          rw [hcE, hl] at hM
          norm_num at hM
        · exact (BottomGrade.bottom_not_nonfree word hw hε1 ((freeH_iff_freeHn (frameAt word) bb).mpr hBH) hbl) hNF
      · exact (LeftVWebProof.left_V_not_nonfree_proved word hw hε1
          ((freeV_iff_freeVn (frameAt word) bb).mpr hBV)) hNF
      · have hRW : RightWit (frameAt word) c :=
          ⟨bb, ha1, ha2, by rw [kernel_eq]; exact (freeV_iff_freeVn (frameAt word) _).mpr hKV⟩
        rcases hWit with hB | hA
        · have hcE := right_bottom_centre (frameAt word) hc hRW hB
          have hl := ColourPacket.lap_MW_dn1 hw hSE
          rw [hcE, hl] at hM
          norm_num at hM
        · rcases hA with ⟨-, hL⟩ | ⟨hεm', -⟩
          · obtain ⟨v', hv1, hv2, hvF⟩ := leftWit_site hL
            exact left_right_excl hn1 hnd hd5 ⟨hv1, hv2⟩ ⟨ha1, ha2⟩ hvF hKV
          · rw [hε1] at hεm'
            norm_num at hεm'
      · have hT : ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧
            freeHn (frameAt word).child.num (frameAt word).child.den
              (w.1 - ((frameAt word).child.num - (frameAt word).child.den),
                w.2 - ((frameAt word).child.num + (frameAt word).child.den)) :=
          ⟨bb, ha1, ha2, hTV⟩
        rcases hWit with hB | hA
        · exact BottomExcl.no_bottom_top hnO hdO hn1 hnd c (bottomWit_site hB) hT
        · rcases hA with ⟨-, hL⟩ | ⟨hεm', -⟩
          · have hcC := classify_plus hnO hdO hn1 hnd hTL c hc (leftWit_site hL) hT
            have hcE : c = ((frameAt word).vLast.1 + 1, (frameAt word).vLast.2) := by
              rw [hcC]
              refine Prod.ext ?_ ?_
              · simp only [ChildFrame.vLast]; ring
              · simp only [ChildFrame.vLast]
            have hl := ColourPacket.lap_MW_vLast hw hSE
            rw [hcE, hl] at hM
            norm_num at hM
          · rw [hε1] at hεm'
            norm_num at hεm'
    · -- the eps = -1 cases
      rcases hspec with hBH | hBV | hKV | hTV
      · exact (BottomGradeNeg.bottom_not_nonfree_neg word hw hεm
          ((freeH_iff_freeHn (frameAt word) bb).mpr hBH)) hNF
      · have hLf : LeftWit (frameAt word) c :=
          ⟨bb, ha1, ha2, (freeV_iff_freeVn (frameAt word) bb).mpr hBV⟩
        rcases hWit with hB | hA
        · have hcE := left_bottom_centre (frameAt word) hc hLf hB
          have hl := laplacian_MW_one_one hw hSE
          rw [hcE, hl] at hM
          norm_num at hM
        · rcases hA with ⟨hε1', -⟩ | ⟨-, hR⟩
          · rw [hεm] at hε1'
            norm_num at hε1'
          · obtain ⟨w', hw1, hw2, hwF⟩ := rightWit_site hR
            exact left_right_excl hn1 hnd hd5 ⟨ha1, ha2⟩ ⟨hw1, hw2⟩ hBV hwF
      · by_cases hz : (bb.1 - (frameAt word).child.den, bb.2 - (frameAt word).child.num) =
            (frameAt word).vLast
        · have hz1 : bb.1 - (frameAt word).child.den =
              (frameAt word).child.num - (frameAt word).child.den + 1 := congrArg Prod.fst hz
          have hz2 : bb.2 - (frameAt word).child.num =
              (frameAt word).child.num + (frameAt word).child.den - 1 := congrArg Prod.snd hz
          have hc1 : |c.1 - ((frameAt word).child.num + 1)| ≤ 1 := by
            rw [abs_le] at ha1 ⊢; constructor <;> omega
          have hc2 : |c.2 - (2 * (frameAt word).child.num + (frameAt word).child.den - 1)| ≤ 1 := by
            rw [abs_le] at ha2 ⊢; constructor <;> omega
          have hcE := FLatticePaper.Exceptions.R_strict_unique hnO hdO hn1 hnd c hc1 hc2 hc
          have hl := ColourPacket.lap_MW_R hw hSE
          rw [hcE, hl] at hM
          norm_num at hM
        · have hz' : (bb.1 - (frameAt word).child.den, bb.2 - (frameAt word).child.num) ∈
              (frameAt word).freeV := (freeV_iff_freeVn (frameAt word) _).mpr hKV
          have nat := LeftVNegGrade.right_up_arc_not_nonfree word hw hεm hz' hz
          have e2 : (bb.1 - (frameAt word).child.den, bb.2 - (frameAt word).child.num) +
              ((frameAt word).child.den, (frameAt word).child.num) = bb := by
            ext <;> simp
          rw [e2] at nat
          exact nat hNF
      · have hT : ∃ w : Site, |w.1 - c.1| ≤ 1 ∧ |w.2 - c.2| ≤ 1 ∧
            freeHn (frameAt word).child.num (frameAt word).child.den
              (w.1 - ((frameAt word).child.num - (frameAt word).child.den),
                w.2 - ((frameAt word).child.num + (frameAt word).child.den)) :=
          ⟨bb, ha1, ha2, hTV⟩
        rcases hWit with hB | hA
        · exact BottomExcl.no_bottom_top hnO hdO hn1 hnd c (bottomWit_site hB) hT
        · rcases hA with ⟨hε1', -⟩ | ⟨-, hR⟩
          · rw [hεm] at hε1'
            norm_num at hε1'
          · have hcC := classify_minus hnO hdO hn1 hnd hTL c hc (rightWit_site hR) hT
            have hl := ColourPacket.lap_MW_R hw hSE
            rw [hcC, hl] at hM
            norm_num at hM
  rcases hcr with hall | ⟨h0, h0'⟩ | ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
  · exact hne' (all_strict_corner hpS hall.1 hall.2.1 hall.2.2.1 hall.2.2.2)
  · exact key (A, B) (corner_mem_all A B).1 h0 h0'
  · exact key (A + 1, B) (corner_mem_all A B).2.1 h1 h1'
  · exact key (A, B + 1) (corner_mem_all A B).2.2.1 h2 h2'
  · exact key (A + 1, B + 1) (corner_mem_all A B).2.2.2 h3 h3'

end FLatticePaper.TopSquare
