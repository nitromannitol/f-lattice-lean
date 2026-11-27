import FLatticePaper.Plane.Induction.ConeTerminal
import FLatticePaper.Plane.Induction.RestrictedFan
import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.OddAxialRank
import FLatticePaper.Plane.Induction.EasyHRankDiag
import FLatticePaper.Plane.Induction.HGap
import FLatticePaper.Plane.Induction.W1Exit

/-! # Rank 4 in the fort form (the fan from `o₂ + U`, the translated fort)

Setting. `S` is a restricted fort (`IsRestrictedFort`, the fort of the no-fort induction), `E` is the set of earlier row labels with
`E ∩ S = ∅`, `U = (d, n)` is the period of the field (`F (z + U) = F z`). The fort is translated, not the claim:
`S' = S + U = {x | x − U ∈ S}` is again a fort at the nonfree sites (`shiftSet_fortAt`), and `o₂ ∈ S` gives the fan start `o₂ + U ∈ S'`.

The fan from the start is the cone fan of `ConeTerminal` (the cap window `cone_window`, the parabola `parabolaField b.2`). Its walk
exit `w` (the first point outside the open rectangle along a walk of the rules `FanRules`) lies in `S'`, so `w − U ∈ S`. The walk
identification `hexit` says every walk exit is an earlier label translated by `U` (verified numerically on the black east-north sites,
267 of 267 branch exits at words ≤ 4). Then `w − U ∈ E ∩ S`, contradicting `E ∩ S = ∅`. Hence `o₂ ∉ S`.

`hexit` is the named walk-identification input (the uniform fan closure, Q1 ALL_WHITE section B). -/

namespace FLatticePaper.Rank4Fort

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FanPropagation FLatticePaper.ContactCone
  FLatticePaper.FreeClosure FLatticePaper.ConeTerminal FLatticePaper.CapRay FLatticePaper.RestrictedFan

/-- The translate of a site set by `v`: `shiftSet v S = {x | x − v ∈ S}`. -/
def shiftSet (v : Site) (S : Set Site) : Set Site := {x | x - v ∈ S}

/-- The period `U` of a child frame is an element of the deck span. -/
theorem uvec_mem_span (frame : ChildFrame) : RowAt.Uvec frame ∈ frame.child.modifiedDeck.span := by
  have h := FLatticePaper.EasyHRank.combine_one_zero_eq_Uvec frame
  exact ⟨1, 0, h.symm⟩

/-- `−U` is in the deck span. -/
theorem uneg_mem_span (frame : ChildFrame) : -RowAt.Uvec frame ∈ frame.child.modifiedDeck.span := by
  refine ⟨-1, 0, ?_⟩
  rw [← FLatticePaper.EasyHRank.combine_one_zero_eq_Uvec frame]
  ext <;> simp [PeriodDeck.combine]

/-- `U` is even (the sum `d + n` is even). -/
theorem evenSite_uvec (frame : ChildFrame) : EvenSite (RowAt.Uvec frame) := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  unfold EvenSite RowAt.Uvec
  dsimp only
  omega

/-- A fort at the nonfree sites is translated to a fort at the nonfree sites by `U`. -/
theorem shiftSet_fortAt (frame : ChildFrame) {F : Field} (hper : ∀ (c : Site) (i j : ℤ),
      laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c)
    {S : Set Site} (hS : FortAt (Nonfree frame) F S) :
    FortAt (Nonfree frame) F (shiftSet (RowAt.Uvec frame) S) := by
  have hlap : ∀ c : Site, laplacian F (c + RowAt.Uvec frame) = laplacian F c := by
    intro c
    have h := hper c 1 0
    rw [FLatticePaper.EasyHRank.combine_one_zero_eq_Uvec frame] at h
    exact h
  have hUeven := evenSite_uvec frame
  intro x hx hN
  have hxS : x - RowAt.Uvec frame ∈ S := hx
  have hNy : Nonfree frame (x - RowAt.Uvec frame) := by
    have := FLatticePaper.PassageRank.nonfree_add_span frame hN (uneg_mem_span frame)
    rwa [show x + -RowAt.Uvec frame = x - RowAt.Uvec frame by abel] at this
  have hlx : laplacian F x = laplacian F (x - RowAt.Uvec frame) := by
    rw [← hlap (x - RowAt.Uvec frame)]
    congr 1
    abel
  have hneg : incomingNeg x - RowAt.Uvec frame = incomingNeg (x - RowAt.Uvec frame) := by
    have h := FLatticePaper.ForcedArrows.incomingNeg_add_even (x := x - RowAt.Uvec frame) hUeven
    rw [show x - RowAt.Uvec frame + RowAt.Uvec frame = x by abel] at h
    rw [h]
    abel
  have hpos : incomingPos x - RowAt.Uvec frame = incomingPos (x - RowAt.Uvec frame) := by
    have h := FLatticePaper.ForcedArrows.incomingPos_add_even (x := x - RowAt.Uvec frame) hUeven
    rw [show x - RowAt.Uvec frame + RowAt.Uvec frame = x by abel] at h
    rw [h]
    abel
  rcases hS (x - RowAt.Uvec frame) hxS hNy with ⟨hl, hA⟩ | ⟨hl, hA, hB⟩
  · refine Or.inl ⟨hlx.trans hl, ?_⟩
    show (incomingNeg x ∈ shiftSet (RowAt.Uvec frame) S ∨ incomingPos x ∈ shiftSet (RowAt.Uvec frame) S)
    rcases hA with h | h
    · left
      show incomingNeg x - RowAt.Uvec frame ∈ S
      rw [hneg]
      exact h
    · right
      show incomingPos x - RowAt.Uvec frame ∈ S
      rw [hpos]
      exact h
  · refine Or.inr ⟨hlx.trans hl, ?_, ?_⟩
    · show incomingNeg x - RowAt.Uvec frame ∈ S
      rw [hneg]
      exact hA
    · show incomingPos x - RowAt.Uvec frame ∈ S
      rw [hpos]
      exact hB

/-! ## The start of the fan at an odd black east-north site -/

/-- **The fan start is a contact.** For an odd free chain point `z` (`n + 2 ≤ t(z) ≤ d − 2`) with black `q = z + (1,1)`, the even
point `w = z + (1,2)` has `F w = capMin 2 = −1`: the east input `z + (1,0)` has `F = 0` (even zero interval), the point `q` has `F = 0`
(zero band), so `laplacian F q = F w = −1`. -/
theorem start_F_value (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {z : Site} (hodd : ¬ EvenSite z) (ht1 : frame.child.num + 2 ≤ frame.tGrade z)
    (ht2 : frame.tGrade z ≤ frame.child.den - 2)
    (hblack : laplacian F (z.1 + 1, z.2 + 1) = -1) :
    F (z.1 + 1, z.2 + 2) = parabolaField z.2 (z.1 + 1, z.2 + 2) := by
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hqodd : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hEev : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have eTE : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have eTQ : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hFE : F (z.1 + 1, z.2) = 0 :=
    hZ _ hEev (by rw [eTE]; linarith) (by rw [eTE]; linarith)
  have hFQ : F (z.1 + 1, z.2 + 1) = 0 :=
    hP.strips.1 _ (by rw [eTQ]; linarith) (by rw [eTQ]; linarith)
  have hNeg : incomingNeg (z.1 + 1, z.2 + 1) = (z.1 + 1, z.2) := by
    unfold incomingNeg
    rw [if_neg hqodd]
    simp
  have hPos : incomingPos (z.1 + 1, z.2 + 1) = (z.1 + 1, z.2 + 2) := by
    unfold incomingPos
    rw [if_neg hqodd]
    simp only [add_assoc]
    norm_num
  unfold laplacian at hblack
  rw [hNeg, hPos, hFE, hFQ] at hblack
  have hcap2 : FLatticePaper.QuadraticCap.capMin 2 = -1 := by
    norm_num [FLatticePaper.QuadraticCap.capMin]
  unfold parabolaField
  rw [show z.2 + 2 - z.2 = 2 by ring, hcap2]
  linarith

/-- **The fan start is in the cone.** For such `z` and `K ≥ 3`, the point `z + (1,2)` is open and a cone root of base `z`. -/
theorem start_open_cone (frame : ChildFrame) (hd2 : 2 * frame.child.num ≤ frame.child.den)
    {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den)
    {K : ℕ} (hK3 : 3 ≤ K) :
    frame.openRect (z.1 + 1, z.2 + 2) ∧ CapRay.ConeRoot z K (z.1 + 1, z.2 + 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
    rw [W1Exit.openRect_iff]
    have hrange := OddAxialRank.odd_t_range frame hz hodd hx2 hxd
    have hcl : z ∈ frame.closedPolygon := by
      simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
      exact hz.1
    have hlow := OddAxialRank.odd_low frame hcl hodd (by omega) hrange.2 hx2
    have hEfree := EasyHRankDiag.east_freeH_of_odd frame hz hodd (by omega) hxd
    have hEev : EvenSite (z.1 + 1, z.2) := by
      unfold EvenSite at hodd ⊢
      dsimp only
      omega
    have hHE := HGap.sGrade_lt_of_freeH_even frame hd2 hEfree hEev
    have eSE : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
      unfold ChildFrame.sGrade
      dsimp only
      ring
    rw [eSE] at hHE
    have hwEven : EvenSite (z.1 + 1, z.2 + 2) := by
      unfold EvenSite at hodd ⊢
      dsimp only
      omega
    have eTw : FLatticePaper.W1.w1t frame.child.num frame.child.den (z.1 + 1, z.2 + 2)
        = frame.tGrade z + frame.child.num - 2 * frame.child.den := by
      unfold FLatticePaper.W1.w1t ChildFrame.tGrade
      dsimp only
      ring
    have eSw : FLatticePaper.W1.w1s frame.child.num frame.child.den (z.1 + 1, z.2 + 2)
        = frame.sGrade z + 3 * frame.child.den - frame.child.num := by
      unfold FLatticePaper.W1.w1s ChildFrame.sGrade
      dsimp only
      ring
    have eA : FLatticePaper.W1.w1b frame.child.num frame.child.den (z.1 + 1, z.2 + 2)
        = frame.child.den + frame.child.num - 2 := by
      unfold FLatticePaper.W1.w1b
      rw [if_pos hwEven]
    have eA2 : FLatticePaper.W1.w1a frame.child.num (z.1 + 1, z.2 + 2) = 2 := by
      unfold FLatticePaper.W1.w1a
      rw [if_pos hwEven]
    have eH : FLatticePaper.W1.w1h frame.child.num frame.child.den (z.1 + 1, z.2 + 2)
        = 2 * frame.child.num := by
      unfold FLatticePaper.W1.w1h
      rw [if_pos hwEven]
    have eC : FLatticePaper.W1.w1c frame.child.num frame.child.den (z.1 + 1, z.2 + 2) = 0 := by
      unfold FLatticePaper.W1.w1c
      rw [if_pos hwEven]
    have eTT : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
      rw [hTd]
      unfold FLatticePaper.W1.w1T
      ring
    have hT : 3 * frame.child.den < frame.child.periodDenominator := by
      rw [hTd]
      nlinarith
    unfold FLatticePaper.W1.StrictInterior
    rw [eA, eA2, eH, eC, eTw, eSw, eTT]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hrange.1, hrange.2]
  · have hwEven : EvenSite (z.1 + 1, z.2 + 2) := by
      unfold EvenSite at hodd ⊢
      dsimp only
      omega
    refine ⟨?_, ?_, fun _ => ?_, fun h => absurd hwEven h⟩
    · show 1 ≤ (z.1 + 1, z.2 + 2).2 - z.2
      dsimp only
      omega
    · show (z.1 + 1, z.2 + 2).2 - z.2 ≤ (K : ℤ) - 1
      dsimp only
      omega
    · show (z.1 + 1, z.2 + 2).1 - z.1 ≥ (z.1 + 1, z.2 + 2).2 - z.2 - 1
      dsimp only
      omega

/-- **Rank 4 at an odd black east-north site (fort form).** `z` is an odd free chain point with `2 ≤ z₁ < d`, the east-north
site `q = z + (1,1)` is black, and the geometric boundary claim `hG` holds for the cone of base `z`: every closed-boundary input of a
cone point is an earlier label translated by `U`. Then `z + (1,2) − U` is not in the restricted fort `S` (the translated fort `S + U`
has the fan start `z + (1,2)`; its first cone exit is an earlier label + `U`, which is not in `S`). -/
theorem rank4_at (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    {p q : ℤ} (hs : frame.child.num * p - frame.child.den * q = 2 - frame.child.num)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (K : ℕ) (hK2 : 2 ≤ K) (hK3 : 3 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKr : 2 * frame.child.num * (K : ℤ) ≤ 3 * frame.child.den + 5 * frame.child.num - 1)
    (hcap : ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (AuxRankQ1.permitsQ1 frame F (-1)) S)
    (Eset : Set Site) (hE : ∀ e ∈ Eset, e ∉ S)
    (z : Site) (hzfree : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den)
    (hblack : laplacian F (z.1 + 1, z.2 + 1) = -1)
    (hG : ∀ x i : Site, (frame.openRect x ∧ CapRay.ConeRoot z K x) → (i = incomingNeg x ∨ i = incomingPos x) →
      i ∈ frame.closedPolygon → ¬ frame.openRect i → ∃ e ∈ Eset, i = e + RowAt.Uvec frame) :
    (z.1 + 1, z.2 + 2) - RowAt.Uvec frame ∉ S := by
  intro h
  have hrange := OddAxialRank.odd_t_range frame hzfree hodd hx2 hxd
  have hstart := start_F_value frame hP hZ hodd hrange.1 hrange.2 hblack
  have hPw := start_open_cone frame hd2 hzfree hodd hx2 hxd hK3
  have hper : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c :=
    fun c i j => laplacian_add_combine hP.periods c i j
  have hv0S : (z.1 + 1, z.2 + 2) ∈ shiftSet (RowAt.Uvec frame) S := by
    show (z.1 + 1, z.2 + 2) - RowAt.Uvec frame ∈ S
    exact h
  have hFS' : FortAt (Nonfree frame) F (shiftSet (RowAt.Uvec frame) S) :=
    shiftSet_fortAt frame hper (fortAt_nonfree_of_restricted frame hS)
  have hPN : ∀ x, (frame.openRect x ∧ CapRay.ConeRoot z K x) → Nonfree frame x :=
    fun x hx => strictInterior_nonfree frame ((W1Exit.openRect_iff frame x).1 hx.1)
  obtain ⟨next, hr⟩ := fan_path_exists_fortAt (P := fun x => frame.openRect x ∧ CapRay.ConeRoot z K x) hFS' hPN
    (parabola_binary z.2) (fun w hw => parabola_lap_even z.2 w hw)
    (cone_window frame hP hsig hs K hcap z hrange.1)
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr (cone_finite frame z K)
    ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩
  cases k with
  | zero => exact absurd hPw (by simpa using hk)
  | succ k' =>
    have hpred := hj k' (Nat.lt_succ_self k')
    have hsucc : next^[k' + 1] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩
        = next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩) :=
      Function.iterate_succ_apply' next k' _
    rw [hsucc] at hk
    have hrk := hr _ hpred
    have hcl : (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 ∈ frame.closedPolygon :=
      FLatticePaper.W1Exit.rectInputs frame _ hpred.1 _ hrk.2
    have hout : ¬ frame.openRect (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 :=
      fun hopen => hk (fan_next_P frame hP hsig hs K hK2 hKs hKr hcap z hrange.1 _ _ hpred hrk.2 hrk.1 hopen
        (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).2.2)
    obtain ⟨e, he, heq⟩ := hG _ _ hpred hrk.2 hcl hout
    have hmem : (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).1 - RowAt.Uvec frame ∈ S :=
      (next (next^[k'] ⟨(z.1 + 1, z.2 + 2), hv0S, hstart⟩)).2.1
    rw [heq, add_sub_cancel_right] at hmem
    exact hE e he hmem

end FLatticePaper.Rank4Fort
